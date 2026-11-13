/*
 * Raumregeln (Platzieren, Begehbarkeit, Werte, Isolation, Stützung) aus Syx-Vis display/planner-core.js,
 * angepasst an die Spieldaten v71. Original:
 * MIT License
 *
 * Copyright (c) 2024 nobody0
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
const PC = (() => {
// Planner core — shared room rules, validation, and utilities for browser planner + optimizer + Node.js scripts

/** Set of availability values that block tile passage (solid + penalty). */
const AVAIL_IMPASSABLE = new Set([
  "SOLID", "NOT_ACCESSIBLE", "ROOM_SOLID",  // truly solid
  "AVOID_PASS", "AVOID_LIKE_FUCK", "PENALTY4", // penalty — still blocks walkability
]);

/** 4-directional neighbor offsets [row, col]. */
const DIRS = [[0, 1], [0, -1], [1, 0], [-1, 0]];

/** 8-directional neighbor offsets [row, col]. */
const DIRS8 = [[0,1],[0,-1],[1,0],[-1,0],[1,1],[1,-1],[-1,1],[-1,-1]];

/** Support ray radius for stability checking. */
const SUPPORT_RADIUS = 4;

/**
 * Stability threshold — tile is stable when tileSupport() >= this value.
 * The game uses exact 1.0 comparison, but its yellow overlay formula
 * (CLAMP(support-1, 0, 4)/4) visually hides sub-epsilon shortfalls.
 * We use a small epsilon to match the game's effective behavior.
 */
const STABILITY_THRESHOLD = 1.0 - 1e-9;

/** Pre-computed DDA support rays (matches game's TileRayTracer.java). */
const SUPPORT_RAYS = [];
{
  const has = Array.from({ length: SUPPORT_RADIUS * 2 + 1 }, () => new Uint8Array(SUPPORT_RADIUS * 2 + 1));
  function ddaRay(fromx, fromy) {
    let x = fromx, y = fromy;
    const ax = Math.abs(x), ay = Math.abs(y);
    const divider = ax > ay ? ax : (ax < ay ? ay : ax);
    if (divider === 0) return;
    const dx = -x / divider, dy = -y / divider;
    let i = 0;
    while (i < divider) {
      const tx = Math.trunc(x), ty = Math.trunc(y);
      if (Math.floor(Math.sqrt(x * x + y * y)) <= SUPPORT_RADIUS) {
        if (has[ty + SUPPORT_RADIUS][tx + SUPPORT_RADIUS]) return;
        has[ty + SUPPORT_RADIUS][tx + SUPPORT_RADIUS] = 1;
        break;
      }
      x += dx; y += dy; i++;
    }
    const coos = [];
    while (true) {
      const tx = Math.trunc(x), ty = Math.trunc(y);
      if (tx === 0 && ty === 0) break;
      coos.push({ dx: tx, dy: ty });
      x += dx; y += dy;
    }
    coos.reverse();
    if (coos.length > 0) SUPPORT_RAYS.push(coos);
  }
  for (let gy = -SUPPORT_RADIUS; gy <= SUPPORT_RADIUS; gy++) {
    ddaRay(-SUPPORT_RADIUS, gy);
    ddaRay(SUPPORT_RADIUS, gy);
  }
  for (let gx = -SUPPORT_RADIUS; gx <= SUPPORT_RADIUS; gx++) {
    ddaRay(gx, -SUPPORT_RADIUS);
    ddaRay(gx, SUPPORT_RADIUS);
  }
}

// ── BFS infrastructure (pointer-based queue + stamp-based visited) ──

/** Create a pointer-based BFS queue backed by Int32Array (avoids O(n) Array.shift). */
function createBFSQueue(capacity) {
  const buf = new Int32Array(capacity * 2);
  let head = 0, tail = 0;
  return {
    push(r, c) { buf[tail++] = r; buf[tail++] = c; },
    shift() { const r = buf[head++], c = buf[head++]; return [r, c]; },
    get length() { return (tail - head) >> 1; },
    reset() { head = 0; tail = 0; },
  };
}

/** Reset visited tracking in O(1) by incrementing stamp. */
function freshVisited(ctx) {
  ctx.visitedStamp++;
  if (ctx.visitedStamp === 0) { ctx.visitedBuf.fill(0); ctx.visitedStamp = 1; }
  return { buf: ctx.visitedBuf, stamp: ctx.visitedStamp, w: ctx.gridW };
}

function visitedHas(v, r, c) { return v.buf[r * v.w + c] === v.stamp; }
function visitedSet(v, r, c) { v.buf[r * v.w + c] = v.stamp; }

// ── Tile rotation / group helpers ────────────────────────

/** Rotate a 2D tile grid 90° clockwise. */
function rotateTiles90CW(tiles) {
  const rows = tiles.length;
  const cols = Math.max(...tiles.map(r => r.length));
  const out = [];
  for (let c = 0; c < cols; c++) {
    const newRow = [];
    for (let r = rows - 1; r >= 0; r--) {
      newRow.push(tiles[r]?.[c] ?? null);
    }
    out.push(newRow);
  }
  return out;
}

/**
 * Get the tile grid for an item at a given rotation (0–3).
 * @param {{ tiles: (string|null)[][] }} item
 * @param {number} rotation
 * @returns {(string|null)[][]}
 */
function getRotatedTiles(item, rotation) {
  let tiles = item.tiles;
  for (let i = 0; i < rotation; i++) tiles = rotateTiles90CW(tiles);
  return tiles;
}

/**
 * Get the list of allowed rotation values for a furniture group.
 * @param {{ rotations: number }} group
 * @returns {number[]}
 */
function getAllowedRotations(group) {
  switch (group.rotations) {
    case 0: return [0];
    case 1: return [0, 1];   // v71: zweite Ausrichtung = 90° im Uhrzeigersinn (FurnisherItemGroup.getRot)
    case 3: return [0, 1, 2, 3];
    default: return [0];
  }
}

// ── Tile cache ──────────────────────────────────────────

/** Get (or compute and cache) rotated tiles for an item. */
function getCachedTiles(ctx, groupIdx, itemIdx, rotation) {
  const key = `${groupIdx}_${itemIdx}_${rotation}`;
  let cached = ctx.tileCache.get(key);
  if (!cached) {
    const item = ctx.furnitureSet.groups[groupIdx]?.items[itemIdx];
    if (!item) return [];
    cached = getRotatedTiles(item, rotation);
    ctx.tileCache.set(key, cached);
  }
  return cached;
}

// ── RoomContext creation ─────────────────────────────────

/**
 * Create a RoomContext with fast data structures for room-rule operations.
 * Both the planner UI and optimizer create contexts and call shared core functions.
 * The optimizer extends the context with additional fields (rng, scoring caches, etc.).
 */
function createRoomContext(furnitureSet, building, room, placements, gridW, gridH, doors) {
  const ctx = {
    furnitureSet, building, gridW, gridH,
    room,
    placements,
    doors,
    occupancy: null,
    tileCache: new Map(),
    blockerCount: Array.from({ length: gridH }, () => new Int8Array(gridW)),
    groupGrid: Array.from({ length: gridH }, () => new Int16Array(gridW).fill(-1)),
    mustReachGrid: new Int8Array(gridW * gridH),
    occupiedCount: 0,
    visitedBuf: new Uint32Array(gridW * gridH), visitedStamp: 0,
    blockedBuf: new Uint32Array(gridW * gridH), blockedStamp: 0,
    bfsQueue: createBFSQueue(gridW * gridH),
    currentStats: null, statsDirty: true,
    mustReachCache: null, mustReachDirty: true,
    stabilityDirty: true,
    _walkabilityValid: false,
    _connectivityVerified: false,
    _doorCandidateCache: undefined,
    groupCounts: null,
    // Stamp buffers for canPlaceFast (zero-allocation placement checks)
    _cpBlockerBuf: new Uint32Array(gridW * gridH),
    _cpBlockerStamp: 0,
    _cpTileBuf: new Uint32Array(gridW * gridH),
    _cpTileStamp: 0,
    _cpTileList: new Int32Array(192),  // [gr, gc] × 96 tiles max
    _cpTileCount: 0,
    _cpCheckedBuf: new Uint32Array(512),  // indexed by placement index
    _cpCheckedStamp: 0,
    // Free-tile bitmap: 1 = room tile AND unoccupied, 0 = otherwise
    freeBitmap: new Uint8Array(gridW * gridH),
  };
  ctx.occupancy = buildOccupancyGrid(ctx);
  return ctx;
}

// ── Occupancy grid ──────────────────────────────────────

/** Build the occupancy grid from scratch. Returns the grid array. */
function buildOccupancyGrid(ctx) {
  const { gridW, gridH, placements, furnitureSet: fs } = ctx;
  const grid = Array.from({ length: gridH }, () => Array(gridW).fill(-1));
  const bc = Array.from({ length: gridH }, () => new Int8Array(gridW));
  const gg = Array.from({ length: gridH }, () => new Int16Array(gridW).fill(-1));
  const mrg = new Int8Array(gridW * gridH);
  let occCount = 0;
  for (let pi = 0; pi < placements.length; pi++) {
    const p = placements[pi];
    const tiles = getCachedTiles(ctx, p.groupIdx, p.itemIdx, p.rotation);
    for (let r = 0; r < tiles.length; r++) {
      for (let c = 0; c < (tiles[r]?.length ?? 0); c++) {
        const tileKey = tiles[r][c];
        if (tileKey === null) continue;
        const gr = p.row + r, gc = p.col + c;
        if (gr >= 0 && gr < gridH && gc >= 0 && gc < gridW) {
          if (grid[gr][gc] < 0) occCount++;
          grid[gr][gc] = pi;
          gg[gr][gc] = p.groupIdx;
          const tt = fs.tileTypes[tileKey];
          if (tt && AVAIL_IMPASSABLE.has(tt.availability)) bc[gr][gc]++;
          if (tt?.mustBeReachable) mrg[gr * gridW + gc] = 1;
        }
      }
    }
  }
  ctx.occupancy = grid;
  ctx.blockerCount = bc;
  ctx.groupGrid = gg;
  ctx.mustReachGrid = mrg;
  ctx.occupiedCount = occCount;
  ctx.statsDirty = true;
  ctx.stabilityDirty = true;
  ctx.mustReachDirty = true;
  ctx._walkabilityValid = false;
  ctx._connectivityVerified = false;
  // Rebuild freeBitmap: room tile AND unoccupied
  if (ctx.freeBitmap) {
    const fb = ctx.freeBitmap;
    for (let r = 0; r < gridH; r++)
      for (let c = 0; c < gridW; c++)
        fb[r * gridW + c] = (ctx.room[r][c] && grid[r][c] < 0) ? 1 : 0;
  }
  return grid;
}

/**
 * Rebuild occupancy grids in-place from placements — zero allocations.
 * Same logic as buildOccupancyGrid but reuses existing grid arrays.
 */
function rebuildOccupancyInPlace(ctx) {
  const { gridW, gridH, placements, furnitureSet: fs } = ctx;
  for (let r = 0; r < gridH; r++) {
    ctx.occupancy[r].fill(-1);
    ctx.blockerCount[r].fill(0);
    ctx.groupGrid[r].fill(-1);
  }
  ctx.mustReachGrid.fill(0);
  let occCount = 0;
  for (let pi = 0; pi < placements.length; pi++) {
    const p = placements[pi];
    const tiles = getCachedTiles(ctx, p.groupIdx, p.itemIdx, p.rotation);
    for (let r = 0; r < tiles.length; r++) {
      for (let c = 0; c < (tiles[r]?.length ?? 0); c++) {
        const tileKey = tiles[r][c];
        if (tileKey === null) continue;
        const gr = p.row + r, gc = p.col + c;
        if (gr >= 0 && gr < gridH && gc >= 0 && gc < gridW) {
          if (ctx.occupancy[gr][gc] < 0) occCount++;
          ctx.occupancy[gr][gc] = pi;
          ctx.groupGrid[gr][gc] = p.groupIdx;
          const tt = fs.tileTypes[tileKey];
          if (tt && AVAIL_IMPASSABLE.has(tt.availability)) ctx.blockerCount[gr][gc]++;
          if (tt?.mustBeReachable) ctx.mustReachGrid[gr * gridW + gc] = 1;
        }
      }
    }
  }
  ctx.occupiedCount = occCount;
  ctx.statsDirty = true;
  ctx.stabilityDirty = true;
  ctx.mustReachDirty = true;
  ctx._walkabilityValid = false;
  ctx._connectivityVerified = false;
  // Rebuild freeBitmap
  if (ctx.freeBitmap) {
    const fb = ctx.freeBitmap;
    for (let r = 0; r < gridH; r++)
      for (let c = 0; c < gridW; c++)
        fb[r * gridW + c] = (ctx.room[r][c] && ctx.occupancy[r][c] < 0) ? 1 : 0;
  }
}

/** Mark a placement's tiles as occupied in the occupancy grid. Returns false if overlap detected. */
function setOccupancy(ctx, pi) {
  const p = ctx.placements[pi];
  const fs = ctx.furnitureSet;
  const tiles = getCachedTiles(ctx, p.groupIdx, p.itemIdx, p.rotation);
  let overlap = false;
  let addedBlockers = false, addedMR = false;
  for (let r = 0; r < tiles.length; r++) {
    for (let c = 0; c < (tiles[r]?.length ?? 0); c++) {
      const tileKey = tiles[r][c];
      if (tileKey === null) continue;
      const gr = p.row + r, gc = p.col + c;
      if (gr < 0 || gr >= ctx.gridH || gc < 0 || gc >= ctx.gridW) { overlap = true; continue; }
      if (!ctx.room[gr][gc]) { overlap = true; continue; }
      if (ctx.occupancy[gr][gc] >= 0 && ctx.occupancy[gr][gc] !== pi) overlap = true;
      if (ctx.occupancy[gr][gc] < 0) ctx.occupiedCount++;
      ctx.occupancy[gr][gc] = pi;
      ctx.groupGrid[gr][gc] = p.groupIdx;
      if (ctx.freeBitmap) ctx.freeBitmap[gr * ctx.gridW + gc] = 0;
      const tt = fs.tileTypes[tileKey];
      if (tt && AVAIL_IMPASSABLE.has(tt.availability)) { ctx.blockerCount[gr][gc]++; addedBlockers = true; }
      if (tt?.mustBeReachable) { ctx.mustReachGrid[gr * ctx.gridW + gc] = 1; addedMR = true; }
    }
  }
  ctx.statsDirty = true;
  if (addedMR) ctx.mustReachDirty = true;
  if (addedBlockers) ctx._walkabilityValid = false;
  return !overlap;
}

/** Clear a placement's tiles from the occupancy grid. */
function clearOccupancy(ctx, pi) {
  const p = ctx.placements[pi];
  const fs = ctx.furnitureSet;
  const tiles = getCachedTiles(ctx, p.groupIdx, p.itemIdx, p.rotation);
  let removedBlockers = false, removedMR = false;
  for (let r = 0; r < tiles.length; r++) {
    for (let c = 0; c < (tiles[r]?.length ?? 0); c++) {
      const tileKey = tiles[r][c];
      if (tileKey === null) continue;
      const gr = p.row + r, gc = p.col + c;
      if (gr >= 0 && gr < ctx.gridH && gc >= 0 && gc < ctx.gridW) {
        if (ctx.occupancy[gr][gc] === pi) {
          ctx.occupancy[gr][gc] = -1;
          ctx.groupGrid[gr][gc] = -1;
          ctx.occupiedCount--;
          if (ctx.freeBitmap && ctx.room[gr][gc]) ctx.freeBitmap[gr * ctx.gridW + gc] = 1;
          const tt = fs.tileTypes[tileKey];
          if (tt && AVAIL_IMPASSABLE.has(tt.availability)) { ctx.blockerCount[gr][gc]--; removedBlockers = true; }
          if (tt?.mustBeReachable) { ctx.mustReachGrid[gr * ctx.gridW + gc] = 0; removedMR = true; }
        }
      }
    }
  }
  ctx.statsDirty = true;
  if (removedMR) ctx.mustReachDirty = true;
  ctx._connectivityVerified = false;
  if (removedBlockers) ctx._walkabilityValid = false;
}

// ── Tile lookup helpers ──────────────────────────────────

/** Get placement index at (row, col) via occupancy grid — O(1). */
function getPlacementAt(ctx, row, col) {
  const pi = ctx.occupancy[row]?.[col];
  return (pi !== undefined && pi >= 0) ? pi : -1;
}

/** Get the FurnitureTileType at (r,c) from existing placements, or null. */
function getFurnitureTileAt(ctx, r, c, skipPi) {
  const pi = ctx.occupancy[r]?.[c];
  if (pi === undefined || pi < 0 || pi === skipPi) return null;
  const p = ctx.placements[pi];
  if (!p) return null;
  const tiles = getCachedTiles(ctx, p.groupIdx, p.itemIdx, p.rotation);
  const lr = r - p.row, lc = c - p.col;
  const tileKey = tiles[lr]?.[lc];
  if (tileKey == null) return null;
  return ctx.furnitureSet.tileTypes[tileKey] || null;
}

/** Check if tile (r,c) is a blocker, considering existing furniture + proposed new blocker tiles. */
// Räume ohne Wand (Food Stall, Eatery, Weide …): eine freie Kachel außerhalb des Raums gilt als Zugang.
// ctx.ext markiert solche Kacheln im lokalen Raster (Bezirksplaner, nicht Syx-Vis).
// Bezirksplaner: Qualität, die von Hilfsmöbeln abhängt (quality() der Instance-Klassen, Spielcode v71).
// Anteil = clamp(mod × Hilfswert ÷ Bezugswert, 0, 1) wie FurnisherStatRelative; Qualität = base + (1 − base) × Anteil.
// Wirksame Leistung = Bezugswert × Qualität (Plätze, Tische, Betten …). Verfall und Wärme (Bad) kommen im Betrieb dazu.
const BZ_QUALITY = {
  lavatory:  { ref: 'latrines', rel: 'basins',     base: 0.5, mod: 1 },   // LavatoryInstance: 0,5 + 0,5 × basins
  canteen:   { ref: 'guests',   rel: 'tables',     base: 0.2, mod: 1 },   // CanteenInstance: 0,2 + 0,8 × tables
  barber:    { ref: 'latrines', rel: 'quality',    base: 0,   mod: 1 },   // barber/Instance: quality
  physician: { ref: 'services', rel: 'quality',    base: 0,   mod: 1 },   // physician/Instance: quality
  tavern:    { ref: 'tables',   rel: 'coziness',   base: 0,   mod: 1 },   // TavernInstance: coziness
  inn:       { ref: 'beds',     rel: 'coziness',   base: 0,   mod: 1 },   // InnInstance: coziness
  pleasure:  { ref: 'beds',     rel: 'coziness',   base: 0,   mod: 1 },   // PleasureInstance: coziness
  bath:      { ref: 'baths',    rel: 'relaxation', base: 0.5, mod: 1.5, extra: 'warmth' },  // BathInstance: (0,5 + 0,5 × relaxation) × (0,5 + 0,5 × Wärme)
  resthome:  { ref: 'stations', rel: 'quality',    base: 0,   mod: 1 },   // Altenheim (seit Version 31): Anteil × (1 − Verfall), Verfall im Betrieb
};
function bzQuality(fs, v) {
  const q = BZ_QUALITY[fs.id]; if (!q) return null;
  const ri = fs.stats.findIndex(st => st.name === q.rel), pi = fs.stats.findIndex(st => st.name === q.ref);
  if (ri < 0 || pi < 0) return null;
  const P = v[pi] || 0, R = v[ri] || 0, share = P > 0 ? Math.min(1, q.mod * R / P) : (R > 0 ? 1 : 0), quality = q.base + (1 - q.base) * share;
  return { ...q, ri, pi, P, R, share, quality, eff: P * quality };
}
function extOk(ctx, r, c) { return !!ctx.ext && r >= 0 && r < ctx.gridH && c >= 0 && c < ctx.gridW && ctx.ext[r * ctx.gridW + c] === 1; }
function isBlockerAt(ctx, r, c, proposedBlockers, skipPi) {
  if (proposedBlockers.has(r * ctx.gridW + c)) return true;
  const tt = getFurnitureTileAt(ctx, r, c, skipPi);
  return tt !== null && AVAIL_IMPASSABLE.has(tt.availability);
}

/** Check if a mustBeReachable tile at (r,c) would have all 4 neighbors blocked. */
function wouldBeFullyBlocked(ctx, r, c, proposedBlockers, skipPi) {
  let blockedCount = 0;
  for (const [dr, dc] of DIRS) {
    const nr = r + dr, nc = c + dc;
    if (nr < 0 || nr >= ctx.gridH || nc < 0 || nc >= ctx.gridW || !ctx.room[nr][nc]) { if (!extOk(ctx, nr, nc)) blockedCount++; }
    else if (isBlockerAt(ctx, nr, nc, proposedBlockers, skipPi)) blockedCount++;
  }
  return blockedCount >= 4;
}

/** Check whether a placed piece (at index pi) has any walkable neighbor. */
function pieceHasWalkableNeighbor(ctx, pi, proposedBlockers, proposedSet, skipPi) {
  const { gridW, gridH, room } = ctx;
  const p = ctx.placements[pi];
  if (!p) return true;
  const tiles = getCachedTiles(ctx, p.groupIdx, p.itemIdx, p.rotation);
  for (let r = 0; r < tiles.length; r++) {
    for (let c = 0; c < (tiles[r]?.length ?? 0); c++) {
      if (tiles[r][c] === null) continue;
      const gr = p.row + r, gc = p.col + c;
      for (const [dr, dc] of DIRS) {
        const nr = gr + dr, nc = gc + dc;
        if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
        if (!room[nr][nc]) { if (extOk(ctx, nr, nc)) return true; continue; }
        if (proposedSet.has(nr * gridW + nc)) continue;
        if (isBlockerAt(ctx, nr, nc, proposedBlockers, skipPi)) continue;
        return true;
      }
    }
  }
  return false;
}

/** Check if adding proposed blockers would split the walkable room into disconnected regions. */
function wouldDisconnectRoom(ctx, proposedBlockers, skipPi) {
  const { gridW, gridH, room } = ctx;
  ctx.blockedStamp++;
  if (ctx.blockedStamp === 0) { ctx.blockedBuf.fill(0); ctx.blockedStamp = 1; }
  const bStamp = ctx.blockedStamp;
  const bBuf = ctx.blockedBuf;
  for (let r = 0; r < gridH; r++)
    for (let c = 0; c < gridW; c++)
      if (ctx.blockerCount[r][c] > 0) bBuf[r * gridW + c] = bStamp;
  if (skipPi !== undefined && skipPi >= 0) {
    const sp = ctx.placements[skipPi];
    if (sp) {
      const stiles = getCachedTiles(ctx, sp.groupIdx, sp.itemIdx, sp.rotation);
      for (let r = 0; r < stiles.length; r++)
        for (let c = 0; c < (stiles[r]?.length ?? 0); c++) {
          if (stiles[r][c] === null) continue;
          const gr = sp.row + r, gc = sp.col + c;
          if (gr >= 0 && gr < gridH && gc >= 0 && gc < gridW) bBuf[gr * gridW + gc] = 0;
        }
    }
  }
  for (const key of proposedBlockers) bBuf[key] = bStamp;

  let totalOpen = 0, startR = -1, startC = -1;
  for (let r = 0; r < gridH; r++)
    for (let c = 0; c < gridW; c++)
      if (room[r][c] && bBuf[r * gridW + c] !== bStamp) {
        totalOpen++;
        if (startR < 0) { startR = r; startC = c; }
      }
  if (totalOpen === 0) return false;

  const v = freshVisited(ctx);
  const q = ctx.bfsQueue;
  q.reset();
  q.push(startR, startC);
  visitedSet(v, startR, startC);
  let reached = 1;
  while (q.length > 0) {
    const [cr, cc] = q.shift();
    for (const [dr, dc] of DIRS) {
      const nr = cr + dr, nc = cc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      if (visitedHas(v, nr, nc) || !room[nr][nc] || bBuf[nr * gridW + nc] === bStamp) continue;
      visitedSet(v, nr, nc);
      reached++;
      q.push(nr, nc);
    }
  }
  return reached < totalOpen;
}

// ── Placement validation ─────────────────────────────────

/**
 * Check if a furniture piece can be placed at (row, col).
 * Returns boolean — fast path for optimizer. Use canPlaceWithReason for UI feedback.
 */
function canPlace(ctx, groupIdx, itemIdx, rotation, row, col, skipPi) {
  const { furnitureSet: fs, gridW, gridH, room, occupancy } = ctx;
  const tiles = getCachedTiles(ctx, groupIdx, itemIdx, rotation);
  if (tiles.length === 0) return false;

  const proposedBlockers = new Set();
  const proposedTiles = [];

  for (let r = 0; r < tiles.length; r++) {
    for (let c = 0; c < (tiles[r]?.length ?? 0); c++) {
      const tileKey = tiles[r][c];
      if (tileKey === null) continue;
      const gr = row + r, gc = col + c;
      if (gr < 0 || gr >= gridH || gc < 0 || gc >= gridW) return false;
      if (!room[gr][gc]) return false;
      const occ = occupancy[gr][gc];
      if (occ >= 0 && occ !== skipPi) return false;
      proposedTiles.push({ gr, gc, tileKey });
      const tt = fs.tileTypes[tileKey];
      if (tt && AVAIL_IMPASSABLE.has(tt.availability)) proposedBlockers.add(gr * gridW + gc);
    }
  }

  // Reject if a blocking tile would cover a reserved tile (door access must stay walkable)
  if (ctx.reservedTiles?.size > 0) {
    for (const { gr, gc, tileKey } of proposedTiles) {
      if (!ctx.reservedTiles.has(gr * gridW + gc)) continue;
      const tt = fs.tileTypes[tileKey];
      if (tt && AVAIL_IMPASSABLE.has(tt.availability)) return false;
    }
  }

  // mustBeReachable check
  for (const { gr, gc, tileKey } of proposedTiles) {
    const tt = fs.tileTypes[tileKey];
    if (!tt?.mustBeReachable) continue;
    let blockedCount = 0;
    for (const [dr, dc] of DIRS) {
      const nr = gr + dr, nc = gc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW || !room[nr][nc]) { if (!extOk(ctx, nr, nc)) blockedCount++; }
      else if (isBlockerAt(ctx, nr, nc, proposedBlockers, skipPi)) blockedCount++;
    }
    if (blockedCount >= 4) return false;
  }

  // Don't fully block existing mustBeReachable tiles
  for (const { gr, gc, tileKey } of proposedTiles) {
    const tt = fs.tileTypes[tileKey];
    if (!tt || !AVAIL_IMPASSABLE.has(tt.availability)) continue;
    for (const [dr, dc] of DIRS) {
      const nr = gr + dr, nc = gc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      const existingTT = getFurnitureTileAt(ctx, nr, nc, skipPi);
      if (existingTT?.mustBeReachable) {
        if (wouldBeFullyBlocked(ctx, nr, nc, proposedBlockers, skipPi)) return false;
      }
    }
  }

  // Piece perimeter reachability
  const proposedSet = new Set(proposedTiles.map(t => t.gr * gridW + t.gc));
  let hasWalkableNeighbor = false;
  for (const { gr, gc } of proposedTiles) {
    if (hasWalkableNeighbor) break;
    for (const [dr, dc] of DIRS) {
      const nr = gr + dr, nc = gc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      if (!room[nr][nc]) { if (extOk(ctx, nr, nc)) { hasWalkableNeighbor = true; break; } continue; }
      if (proposedSet.has(nr * gridW + nc)) continue;
      if (isBlockerAt(ctx, nr, nc, proposedBlockers, skipPi)) continue;
      hasWalkableNeighbor = true;
      break;
    }
  }
  if (!hasWalkableNeighbor) return false;

  // Don't enclose adjacent pieces
  if (proposedBlockers.size > 0) {
    const checkedPieces = new Set();
    for (const { gr, gc, tileKey } of proposedTiles) {
      const tt = fs.tileTypes[tileKey];
      if (!tt || !AVAIL_IMPASSABLE.has(tt.availability)) continue;
      for (const [dr, dc] of DIRS) {
        const nr = gr + dr, nc = gc + dc;
        if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
        const adjPi = occupancy[nr][nc];
        if (adjPi < 0 || adjPi === skipPi || checkedPieces.has(adjPi)) continue;
        checkedPieces.add(adjPi);
        if (!pieceHasWalkableNeighbor(ctx, adjPi, proposedBlockers, proposedSet, skipPi)) return false;
      }
    }
  }

  // Connectivity check
  if (proposedBlockers.size > 0) {
    if (wouldDisconnectRoom(ctx, proposedBlockers, skipPi)) return false;
  }

  return true;
}

/**
 * Fast canPlace using stamp buffers — zero allocations per call.
 * Same logic as canPlace but uses ctx._cp* stamp buffers instead of Set/Array.
 * For optimizer hot paths only; canPlace/canPlaceWithReason stay for UI.
 */
function canPlaceFast(ctx, groupIdx, itemIdx, rotation, row, col, skipPi, skipBFS) {
  const { furnitureSet: fs, gridW, gridH, room, occupancy } = ctx;
  const tiles = getCachedTiles(ctx, groupIdx, itemIdx, rotation);
  if (tiles.length === 0) return false;

  // Advance stamps
  ctx._cpBlockerStamp++;
  if (ctx._cpBlockerStamp === 0) { ctx._cpBlockerBuf.fill(0); ctx._cpBlockerStamp = 1; }
  ctx._cpTileStamp++;
  if (ctx._cpTileStamp === 0) { ctx._cpTileBuf.fill(0); ctx._cpTileStamp = 1; }
  const bStamp = ctx._cpBlockerStamp;
  const bBuf = ctx._cpBlockerBuf;
  const tStamp = ctx._cpTileStamp;
  const tBuf = ctx._cpTileBuf;
  let tCount = 0;
  let blockerCount = 0;

  for (let r = 0; r < tiles.length; r++) {
    for (let c = 0; c < (tiles[r]?.length ?? 0); c++) {
      const tileKey = tiles[r][c];
      if (tileKey === null) continue;
      const gr = row + r, gc = col + c;
      if (gr < 0 || gr >= gridH || gc < 0 || gc >= gridW) return false;
      if (!room[gr][gc]) return false;
      const occ = occupancy[gr][gc];
      if (occ >= 0 && occ !== skipPi) return false;
      const key = gr * gridW + gc;
      ctx._cpTileList[tCount * 2] = gr;
      ctx._cpTileList[tCount * 2 + 1] = gc;
      tBuf[key] = tStamp;
      tCount++;
      const tt = fs.tileTypes[tileKey];
      if (tt && AVAIL_IMPASSABLE.has(tt.availability)) {
        bBuf[key] = bStamp;
        blockerCount++;
      }
    }
  }

  // Reserved tile check
  if (ctx.reservedTiles?.size > 0) {
    for (let i = 0; i < tCount; i++) {
      const gr = ctx._cpTileList[i * 2], gc = ctx._cpTileList[i * 2 + 1];
      const key = gr * gridW + gc;
      if (!ctx.reservedTiles.has(key)) continue;
      if (bBuf[key] === bStamp) return false;  // blocker on reserved tile
    }
  }

  // mustBeReachable check (inline wouldBeFullyBlocked)
  for (let i = 0; i < tCount; i++) {
    const gr = ctx._cpTileList[i * 2], gc = ctx._cpTileList[i * 2 + 1];
    const key = gr * gridW + gc;
    // Get tileType from tileKey — re-derive from tiles grid
    const lr = gr - row, lc = gc - col;
    const tileKey = tiles[lr][lc];
    const tt = fs.tileTypes[tileKey];
    if (!tt?.mustBeReachable) continue;
    let bc = 0;
    for (const [dr, dc] of DIRS) {
      const nr = gr + dr, nc = gc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW || !room[nr][nc]) { if (!extOk(ctx, nr, nc)) bc++; continue; }
      // inline isBlockerAt with stamp
      const nk = nr * gridW + nc;
      if (bBuf[nk] === bStamp) { bc++; continue; }
      const ntt = getFurnitureTileAt(ctx, nr, nc, skipPi);
      if (ntt !== null && AVAIL_IMPASSABLE.has(ntt.availability)) bc++;
    }
    if (bc >= 4) return false;
  }

  // Don't fully block existing mustBeReachable tiles
  for (let i = 0; i < tCount; i++) {
    const gr = ctx._cpTileList[i * 2], gc = ctx._cpTileList[i * 2 + 1];
    const key = gr * gridW + gc;
    if (bBuf[key] !== bStamp) continue;  // not a blocker tile
    for (const [dr, dc] of DIRS) {
      const nr = gr + dr, nc = gc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      const existingTT = getFurnitureTileAt(ctx, nr, nc, skipPi);
      if (!existingTT?.mustBeReachable) continue;
      // inline wouldBeFullyBlocked with stamp
      let bc2 = 0;
      for (const [dr2, dc2] of DIRS) {
        const nr2 = nr + dr2, nc2 = nc + dc2;
        if (nr2 < 0 || nr2 >= gridH || nc2 < 0 || nc2 >= gridW || !room[nr2][nc2]) { bc2++; continue; }
        const nk2 = nr2 * gridW + nc2;
        if (bBuf[nk2] === bStamp) { bc2++; continue; }
        const ntt2 = getFurnitureTileAt(ctx, nr2, nc2, skipPi);
        if (ntt2 !== null && AVAIL_IMPASSABLE.has(ntt2.availability)) bc2++;
      }
      if (bc2 >= 4) return false;
    }
  }

  // Piece perimeter reachability (using tBuf stamp for proposedSet, bBuf for blockers)
  let hasWalkableNeighbor = false;
  for (let i = 0; i < tCount && !hasWalkableNeighbor; i++) {
    const gr = ctx._cpTileList[i * 2], gc = ctx._cpTileList[i * 2 + 1];
    for (const [dr, dc] of DIRS) {
      const nr = gr + dr, nc = gc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      if (!room[nr][nc]) { if (extOk(ctx, nr, nc)) { hasWalkableNeighbor = true; break; } continue; }
      const nk = nr * gridW + nc;
      if (tBuf[nk] === tStamp) continue;  // part of proposed tiles
      if (bBuf[nk] === bStamp) continue;   // proposed blocker
      const ntt = getFurnitureTileAt(ctx, nr, nc, skipPi);
      if (ntt !== null && AVAIL_IMPASSABLE.has(ntt.availability)) continue;
      hasWalkableNeighbor = true;
      break;
    }
  }
  if (!hasWalkableNeighbor) return false;

  // Don't enclose adjacent pieces
  if (blockerCount > 0) {
    ctx._cpCheckedStamp++;
    if (ctx._cpCheckedStamp === 0) { ctx._cpCheckedBuf.fill(0); ctx._cpCheckedStamp = 1; }
    // Grow buffer if needed
    if (ctx._cpCheckedBuf.length < ctx.placements.length + 64) {
      ctx._cpCheckedBuf = new Uint32Array(ctx.placements.length + 256);
      ctx._cpCheckedStamp = 1;
    }
    const cStamp = ctx._cpCheckedStamp;
    const cBuf = ctx._cpCheckedBuf;

    for (let i = 0; i < tCount; i++) {
      const gr = ctx._cpTileList[i * 2], gc = ctx._cpTileList[i * 2 + 1];
      const key = gr * gridW + gc;
      if (bBuf[key] !== bStamp) continue;  // only check blocker tiles
      for (const [dr, dc] of DIRS) {
        const nr = gr + dr, nc = gc + dc;
        if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
        const adjPi = occupancy[nr][nc];
        if (adjPi < 0 || adjPi === skipPi) continue;
        if (cBuf[adjPi] === cStamp) continue;
        cBuf[adjPi] = cStamp;
        // inline pieceHasWalkableNeighbor with stamps
        const ap = ctx.placements[adjPi];
        if (!ap) continue;
        const aTiles = getCachedTiles(ctx, ap.groupIdx, ap.itemIdx, ap.rotation);
        let pieceWalkable = false;
        for (let ar = 0; ar < aTiles.length && !pieceWalkable; ar++) {
          for (let ac = 0; ac < (aTiles[ar]?.length ?? 0) && !pieceWalkable; ac++) {
            if (aTiles[ar][ac] === null) continue;
            const agr = ap.row + ar, agc = ap.col + ac;
            for (const [dr2, dc2] of DIRS) {
              const anr = agr + dr2, anc = agc + dc2;
              if (anr < 0 || anr >= gridH || anc < 0 || anc >= gridW) continue;
              if (!room[anr][anc]) continue;
              const ank = anr * gridW + anc;
              if (tBuf[ank] === tStamp) continue;
              if (bBuf[ank] === bStamp) continue;
              const antt = getFurnitureTileAt(ctx, anr, anc, skipPi);
              if (antt !== null && AVAIL_IMPASSABLE.has(antt.availability)) continue;
              pieceWalkable = true;
              break;
            }
          }
        }
        if (!pieceWalkable) return false;
      }
    }

    // Connectivity check using stamp-based blocker iteration
    if (!skipBFS) {
      if (wouldDisconnectRoomOpt(ctx, bBuf, bStamp, tCount, skipPi)) return false;
      ctx._connectivityVerified = true;
    }
  }

  return true;
}

/**
 * Optimized wouldDisconnectRoom that reads blocker positions from stamp buffer.
 * Iterates _cpTileList to find which tiles are blockers via bBuf check.
 */
function wouldDisconnectRoomOpt(ctx, bBuf, bStamp, tCount, skipPi) {
  const { gridW, gridH, room } = ctx;
  ctx.blockedStamp++;
  if (ctx.blockedStamp === 0) { ctx.blockedBuf.fill(0); ctx.blockedStamp = 1; }
  const dStamp = ctx.blockedStamp;
  const dBuf = ctx.blockedBuf;
  for (let r = 0; r < gridH; r++)
    for (let c = 0; c < gridW; c++)
      if (ctx.blockerCount[r][c] > 0) dBuf[r * gridW + c] = dStamp;
  if (skipPi !== undefined && skipPi >= 0) {
    const sp = ctx.placements[skipPi];
    if (sp) {
      const stiles = getCachedTiles(ctx, sp.groupIdx, sp.itemIdx, sp.rotation);
      for (let r = 0; r < stiles.length; r++)
        for (let c = 0; c < (stiles[r]?.length ?? 0); c++) {
          if (stiles[r][c] === null) continue;
          const gr = sp.row + r, gc = sp.col + c;
          if (gr >= 0 && gr < gridH && gc >= 0 && gc < gridW) dBuf[gr * gridW + gc] = 0;
        }
    }
  }
  // Mark proposed blockers from stamp buffer
  for (let i = 0; i < tCount; i++) {
    const gr = ctx._cpTileList[i * 2], gc = ctx._cpTileList[i * 2 + 1];
    const key = gr * gridW + gc;
    if (bBuf[key] === bStamp) dBuf[key] = dStamp;
  }

  let totalOpen = 0, startR = -1, startC = -1;
  for (let r = 0; r < gridH; r++)
    for (let c = 0; c < gridW; c++)
      if (room[r][c] && dBuf[r * gridW + c] !== dStamp) {
        totalOpen++;
        if (startR < 0) { startR = r; startC = c; }
      }
  if (totalOpen === 0) return false;

  const v = freshVisited(ctx);
  const q = ctx.bfsQueue;
  q.reset();
  q.push(startR, startC);
  visitedSet(v, startR, startC);
  let reached = 1;
  while (q.length > 0) {
    const [cr, cc] = q.shift();
    for (const [dr, dc] of DIRS) {
      const nr = cr + dr, nc = cc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      if (visitedHas(v, nr, nc) || !room[nr][nc] || dBuf[nr * gridW + nc] === dStamp) continue;
      visitedSet(v, nr, nc);
      reached++;
      q.push(nr, nc);
    }
  }
  return reached < totalOpen;
}

/**
 * Check if a furniture piece can be placed, returning a reason string for UI feedback.
 * Same logic as canPlace but returns {ok, reason} instead of boolean.
 */
function canPlaceWithReason(ctx, groupIdx, itemIdx, rotation, row, col) {
  const { furnitureSet: fs, gridW, gridH, room, occupancy } = ctx;
  const tiles = getCachedTiles(ctx, groupIdx, itemIdx, rotation);
  if (tiles.length === 0) return { ok: false, reason: "Invalid item" };

  const proposedBlockers = new Set();
  const proposedTiles = [];

  for (let r = 0; r < tiles.length; r++) {
    for (let c = 0; c < (tiles[r]?.length ?? 0); c++) {
      const tileKey = tiles[r][c];
      if (tileKey === null) continue;
      const gr = row + r, gc = col + c;
      if (gr < 0 || gr >= gridH || gc < 0 || gc >= gridW) return { ok: false, reason: "Out of bounds" };
      if (!room[gr][gc]) return { ok: false, reason: "Not on room tile" };
      const occ = occupancy[gr][gc];
      if (occ >= 0) return { ok: false, reason: "Overlaps furniture" };
      proposedTiles.push({ gr, gc, tileKey });
      const tt = fs.tileTypes[tileKey];
      if (tt && AVAIL_IMPASSABLE.has(tt.availability)) proposedBlockers.add(gr * gridW + gc);
    }
  }

  for (const { gr, gc, tileKey } of proposedTiles) {
    const tt = fs.tileTypes[tileKey];
    if (!tt?.mustBeReachable) continue;
    let blockedCount = 0;
    for (const [dr, dc] of DIRS) {
      const nr = gr + dr, nc = gc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW || !room[nr][nc]) { if (!extOk(ctx, nr, nc)) blockedCount++; }
      else if (isBlockerAt(ctx, nr, nc, proposedBlockers, -1)) blockedCount++;
    }
    if (blockedCount >= 4) return { ok: false, reason: "Would block a reachable tile" };
  }

  for (const { gr, gc, tileKey } of proposedTiles) {
    const tt = fs.tileTypes[tileKey];
    if (!tt || !AVAIL_IMPASSABLE.has(tt.availability)) continue;
    for (const [dr, dc] of DIRS) {
      const nr = gr + dr, nc = gc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      const existingTT = getFurnitureTileAt(ctx, nr, nc, -1);
      if (existingTT?.mustBeReachable) {
        if (wouldBeFullyBlocked(ctx, nr, nc, proposedBlockers, -1)) return { ok: false, reason: "Would block existing furniture" };
      }
    }
  }

  const proposedSet = new Set(proposedTiles.map(t => `${t.gr},${t.gc}`));
  let hasWalkableNeighbor = false;
  for (const { gr, gc } of proposedTiles) {
    if (hasWalkableNeighbor) break;
    for (const [dr, dc] of DIRS) {
      const nr = gr + dr, nc = gc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      if (!room[nr][nc]) { if (extOk(ctx, nr, nc)) { hasWalkableNeighbor = true; break; } continue; }
      if (proposedSet.has(`${nr},${nc}`)) continue;
      if (isBlockerAt(ctx, nr, nc, new Set(), -1)) continue;
      hasWalkableNeighbor = true;
      break;
    }
  }
  if (!hasWalkableNeighbor) return { ok: false, reason: "Furniture would be fully enclosed" };

  if (proposedBlockers.size > 0) {
    if (wouldDisconnectRoom(ctx, proposedBlockers, -1)) return { ok: false, reason: "Would split room" };
  }

  return { ok: true, reason: "" };
}

// ── Walkability check ────────────────────────────────────

/** Full walkability check: connectivity + mustBeReachable + piece reachability. Returns boolean. */
function checkWalkability(ctx) {
  if (ctx._walkabilityValid) return true;
  const { furnitureSet: fs, gridW, gridH, room, placements, blockerCount } = ctx;

  let mustReach;
  if (!ctx.mustReachDirty && ctx.mustReachCache) {
    mustReach = ctx.mustReachCache;
  } else {
    mustReach = [];
    for (const p of placements) {
      const tiles = getCachedTiles(ctx, p.groupIdx, p.itemIdx, p.rotation);
      for (let r = 0; r < tiles.length; r++)
        for (let c = 0; c < (tiles[r]?.length ?? 0); c++) {
          const tileKey = tiles[r][c];
          if (tileKey === null) continue;
          const gr = p.row + r, gc = p.col + c;
          if (gr < 0 || gr >= gridH || gc < 0 || gc >= gridW) continue;
          const tt = fs.tileTypes[tileKey];
          if (tt?.mustBeReachable) mustReach.push({ row: gr, col: gc });
        }
    }
    ctx.mustReachCache = mustReach;
    ctx.mustReachDirty = false;
  }

  // Light path: connectivity already verified by canPlaceFast BFS
  if (ctx._connectivityVerified) {
    ctx._connectivityVerified = false;
    // mustBeReachable: adjacent to non-blocked room tile?
    for (const { row, col } of mustReach) {
      let ok = false;
      for (const [dr, dc] of DIRS) {
        const nr = row + dr, nc = col + dc;
        if (nr >= 0 && nr < gridH && nc >= 0 && nc < gridW
            && ((room[nr][nc] && blockerCount[nr][nc] === 0) || extOk(ctx, nr, nc))) { ok = true; break; }
      }
      if (!ok) return false;
    }
    // Piece reachability: any tile adjacent to non-blocked room tile?
    for (const p of placements) {
      const pTiles = getCachedTiles(ctx, p.groupIdx, p.itemIdx, p.rotation);
      let pieceOk = false;
      for (let r = 0; r < pTiles.length && !pieceOk; r++)
        for (let c = 0; c < (pTiles[r]?.length ?? 0) && !pieceOk; c++) {
          if (pTiles[r][c] === null) continue;
          const gr = p.row + r, gc = p.col + c;
          for (const [dr, dc] of DIRS) {
            const nr = gr + dr, nc = gc + dc;
            if (nr >= 0 && nr < gridH && nc >= 0 && nc < gridW
                && ((room[nr][nc] && blockerCount[nr][nc] === 0) || extOk(ctx, nr, nc))) { pieceOk = true; break; }
          }
        }
      if (!pieceOk) return false;
    }
    ctx._walkabilityValid = true;
    return true;
  }

  // Full BFS path
  const v = freshVisited(ctx);
  const q = ctx.bfsQueue;
  q.reset();
  let totalOpen = 0;
  let seeded = false;
  for (let r = 0; r < gridH; r++)
    for (let c = 0; c < gridW; c++)
      if (room[r][c] && blockerCount[r][c] === 0) {
        totalOpen++;
        if (!seeded) { q.push(r, c); visitedSet(v, r, c); seeded = true; }
      }

  let reached = seeded ? 1 : 0;
  while (q.length > 0) {
    const [cr, cc] = q.shift();
    for (const [dr, dc] of DIRS) {
      const nr = cr + dr, nc = cc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      if (visitedHas(v, nr, nc) || !room[nr][nc] || blockerCount[nr][nc] > 0) continue;
      visitedSet(v, nr, nc);
      reached++;
      q.push(nr, nc);
    }
  }

  for (const { row, col } of mustReach) {
    let reachable = false;
    for (const [dr, dc] of DIRS) {
      const nr = row + dr, nc = col + dc;
      if (nr >= 0 && nr < gridH && nc >= 0 && nc < gridW && (visitedHas(v, nr, nc) || extOk(ctx, nr, nc))) {
        reachable = true; break;
      }
    }
    if (!reachable) return false;
  }

  for (const p of placements) {
    const pTiles = getCachedTiles(ctx, p.groupIdx, p.itemIdx, p.rotation);
    let pieceReachable = false;
    for (let r = 0; r < pTiles.length && !pieceReachable; r++)
      for (let c = 0; c < (pTiles[r]?.length ?? 0) && !pieceReachable; c++) {
        if (pTiles[r][c] === null) continue;
        const gr = p.row + r, gc = p.col + c;
        for (const [dr, dc] of DIRS) {
          const nr = gr + dr, nc = gc + dc;
          if (nr >= 0 && nr < gridH && nc >= 0 && nc < gridW && (visitedHas(v, nr, nc) || extOk(ctx, nr, nc))) {
            pieceReachable = true; break;
          }
        }
      }
    if (!pieceReachable) return false;
  }

  const walkable = reached >= totalOpen;
  if (walkable) ctx._walkabilityValid = true;
  return walkable;
}

/** Diagnostic walkability check returning unreachable MR tiles. Read-only (no cache mutation). */
function findUnreachableMRTiles(ctx) {
  const { furnitureSet: fs, gridW, gridH, room, placements, blockerCount } = ctx;

  // BFS over walkable (non-blocked room) tiles
  const v = freshVisited(ctx);
  const q = ctx.bfsQueue;
  q.reset();
  let totalOpen = 0, seeded = false;
  for (let r = 0; r < gridH; r++)
    for (let c = 0; c < gridW; c++)
      if (room[r][c] && blockerCount[r][c] === 0) {
        totalOpen++;
        if (!seeded) { q.push(r, c); visitedSet(v, r, c); seeded = true; }
      }

  let reached = seeded ? 1 : 0;
  while (q.length > 0) {
    const [cr, cc] = q.shift();
    for (const [dr, dc] of DIRS) {
      const nr = cr + dr, nc = cc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      if (visitedHas(v, nr, nc) || !room[nr][nc] || blockerCount[nr][nc] > 0) continue;
      visitedSet(v, nr, nc);
      reached++;
      q.push(nr, nc);
    }
  }

  const disconnected = totalOpen - reached;

  // Collect mustBeReachable tiles not adjacent to any BFS-visited tile
  const unreachable = [];
  for (const p of placements) {
    const tiles = getCachedTiles(ctx, p.groupIdx, p.itemIdx, p.rotation);
    for (let r = 0; r < tiles.length; r++)
      for (let c = 0; c < (tiles[r]?.length ?? 0); c++) {
        const tileKey = tiles[r][c];
        if (tileKey === null) continue;
        const gr = p.row + r, gc = p.col + c;
        if (gr < 0 || gr >= gridH || gc < 0 || gc >= gridW) continue;
        const tt = fs.tileTypes[tileKey];
        if (!tt?.mustBeReachable) continue;
        let ok = false;
        for (const [dr, dc] of DIRS) {
          const nr = gr + dr, nc = gc + dc;
          if (nr >= 0 && nr < gridH && nc >= 0 && nc < gridW && (visitedHas(v, nr, nc) || extOk(ctx, nr, nc))) {
            ok = true; break;
          }
        }
        if (!ok) unreachable.push({ row: gr, col: gc });
      }
  }

  return { ok: unreachable.length === 0 && disconnected === 0, unreachable, disconnected };
}

// ── Room connectivity ────────────────────────────────────

/** Check that all room tiles form a single connected component. */
function checkRoomConnectivity(ctx) {
  const { gridW, gridH, room } = ctx;
  let totalRoom = 0, startR = -1, startC = -1;
  for (let r = 0; r < gridH; r++)
    for (let c = 0; c < gridW; c++)
      if (room[r][c]) { totalRoom++; if (startR < 0) { startR = r; startC = c; } }
  if (totalRoom === 0) return true;

  const v = freshVisited(ctx);
  const q = ctx.bfsQueue;
  q.reset();
  q.push(startR, startC);
  visitedSet(v, startR, startC);
  let reached = 1;
  while (q.length > 0) {
    const [cr, cc] = q.shift();
    for (const [dr, dc] of DIRS) {
      const nr = cr + dr, nc = cc + dc;
      if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) continue;
      if (visitedHas(v, nr, nc) || !room[nr][nc]) continue;
      visitedSet(v, nr, nc);
      reached++;
      q.push(nr, nc);
    }
  }
  return reached >= totalRoom;
}

// ── Metric functions ─────────────────────────────────────

/** Compute stat totals from placements. Returns array parallel to furnitureSet.stats. */
function computeStats(ctx) {
  const { furnitureSet: fs, building: bld, placements } = ctx;
  if (!fs.stats || !bld.items) return new Array(fs.stats?.length ?? 0).fill(0);
  const totals = new Array(fs.stats.length).fill(0);
  for (const p of placements) {
    const item = fs.groups[p.groupIdx]?.items[p.itemIdx];
    if (!item) continue;
    const bItem = bld.items[p.groupIdx];
    if (!bItem || !bItem.stats) continue;
    const mult = item.multiplierStats ?? item.multiplier;
    for (let s = 0; s < bItem.stats.length && s < totals.length; s++)
      totals[s] += bItem.stats[s] * mult;
  }
  return totals;
}

/** Compute wall tile grid (non-room tiles adjacent to room, excluding doors). */
function computeWalls(ctx) {
  const { gridW, gridH, room, doors } = ctx;
  const walls = Array.from({ length: gridH }, () => Array(gridW).fill(false));
  if (!ctx.furnitureSet?.mustBeIndoors) return walls;
  for (let r = 0; r < gridH; r++) {
    for (let c = 0; c < gridW; c++) {
      if (room[r][c]) continue;
      let adjRoom = false;
      for (const [dr, dc] of DIRS8) {
        const nr = r + dr, nc = c + dc;
        if (nr >= 0 && nr < gridH && nc >= 0 && nc < gridW && room[nr][nc]) {
          adjRoom = true; break;
        }
      }
      if (adjRoom && !doors.has(`${r},${c}`)) walls[r][c] = true;
    }
  }
  // Clean up doors no longer on perimeter
  for (const key of [...doors]) {
    const [r, c] = key.split(",").map(Number);
    let adj = false;
    for (const [dr, dc] of DIRS8) {
      const nr = r + dr, nc = c + dc;
      if (nr >= 0 && nr < gridH && nc >= 0 && nc < gridW && room[nr][nc]) {
        adj = true; break;
      }
    }
    if (!adj || room[r]?.[c]) doors.delete(key);
  }
  return walls;
}

/**
 * Isolation wie im Spiel (v71, settlement/room/main/util/RoomIsolation.getProspect):
 * Randkacheln = Raumkacheln mit mindestens einem Nicht-Raum-Nachbarn (8 Richtungen).
 * Jede Nachbarkachel außerhalb des Raums, die keine Wand ist (z. B. eine Tür), zählt einmal als Lücke.
 * Frei sind ceil(Randkacheln / 10) Lücken. Isolation = ((Rand - Lücken + frei) / Rand) ^ 1,5, höchstens 1.
 * Im Planer ist jede Nicht-Raum-Kachel im Wandring eine Wand, außer den Türen.
 */
function isolationInfo(ctx) {
  if (!ctx.furnitureSet?.mustBeIndoors) return { iso: 1, edge: 0, free: 0, gaps: 0, factor: 1 };
  const { gridW, gridH, room, doors } = ctx;
  const inRoom = (r, c) => r >= 0 && r < gridH && c >= 0 && c < gridW && room[r][c];
  let edge = 0, gaps = 0;
  const seen = new Set();
  for (let r = 0; r < gridH; r++)
    for (let c = 0; c < gridW; c++) {
      if (!room[r][c]) continue;
      let isEdge = false;
      for (const [dr, dc] of DIRS8) if (!inRoom(r + dr, c + dc)) { isEdge = true; break; }
      if (!isEdge) continue;
      edge++;
      for (const [dr, dc] of DIRS8) {
        const nr = r + dr, nc = c + dc;
        if (nr < 0 || nr >= gridH || nc < 0 || nc >= gridW) { gaps++; continue; }
        if (room[nr][nc]) continue;
        const key = `${nr},${nc}`;
        if (!doors.has(key) || seen.has(key)) continue; // Wand oder schon gezählt
        seen.add(key); gaps++;
      }
    }
  if (edge === 0) return { iso: 1, edge: 0, free: 0, gaps: 0, factor: 1 };
  const free = Math.ceil(edge / 10);
  const iso = Math.pow(Math.min(1, Math.max(0, (edge - gaps + free) / edge)), 1.5);
  // Wartung (settlement/maintenance/ROOM_DEGRADER.rate): Aufträge und Material x (1 + 2 x (1 - Isolation))
  return { iso, edge, free, gaps, factor: 1 + 2 * (1 - iso) };
}

/** Isolation 0–1 wie im Spiel. */
function computeIsolation(ctx) {
  return isolationInfo(ctx).iso;
}

const _tileSupportBuf = new Int32Array(128);

/** Compute support value for a single tile (uses DDA support rays). */
function tileSupport(room, gridW, gridH, r, c) {
  let checkedLen = 0;
  let support = 0;
  for (const ray of SUPPORT_RAYS) {
    for (let i = 0; i < ray.length; i++) {
      const tr = r + ray[i].dy, tc = c + ray[i].dx;
      if (tr < 0 || tr >= gridH || tc < 0 || tc >= gridW) break;
      if (!room[tr][tc]) {
        const key = tr * gridW + tc;
        let found = false;
        for (let j = 0; j < checkedLen; j++) {
          if (_tileSupportBuf[j] === key) { found = true; break; }
        }
        if (!found) {
          _tileSupportBuf[checkedLen++] = key;
          support += Math.max(0, (3.5 - i) / 3.5);
        }
        break;
      }
    }
  }
  return support;
}

/** Count group placements using cached counts or linear scan. */
function countGroupPlacements(ctx, groupIdx) {
  if (ctx.groupCounts) return ctx.groupCounts[groupIdx] ?? 0;
  let count = 0;
  for (const p of ctx.placements) if (p.groupIdx === groupIdx) count++;
  return count;
}


return { BZ_QUALITY, bzQuality, extOk, AVAIL_IMPASSABLE, DIRS, DIRS8, STABILITY_THRESHOLD, SUPPORT_RADIUS, SUPPORT_RAYS, _tileSupportBuf, buildOccupancyGrid, canPlace, canPlaceFast, canPlaceWithReason, checkRoomConnectivity, checkWalkability, clearOccupancy, computeIsolation, isolationInfo, computeStats, computeWalls, countGroupPlacements, createBFSQueue, createRoomContext, findUnreachableMRTiles, freshVisited, getAllowedRotations, getCachedTiles, getFurnitureTileAt, getPlacementAt, getRotatedTiles, isBlockerAt, pieceHasWalkableNeighbor, rebuildOccupancyInPlace, rotateTiles90CW, setOccupancy, tileSupport, visitedHas, visitedSet, wouldBeFullyBlocked, wouldDisconnectRoom, wouldDisconnectRoomOpt };
})();
