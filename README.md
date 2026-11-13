# Syx Pack

A browser planner for **Songs of Syx** (game version 0.71.44 / v71). Plan districts, furnish rooms, check production and costs, and move layouts between the planner and the game via the **Better Blueprints** mod.

**Open it:** https://notnotbene.github.io/syx-pack/

No installation, no account. Everything runs in your browser.

## What it does

- **Plan districts:** rooms with automatic walls, roads, walls, doors, ceilings, fixed-size rooms (hearth, well, shrines, monuments …) and rows of houses.
- **Furnish rooms:** furniture editor with game rules, workers, efficiency, isolation and quality; auto-furnish optimizer.
- **Templates:** built-in kit for 37 × 37 blocks, street-grid generator, your own templates with categories.
- **Economy:** production and consumption per day, building costs, upkeep, bonuses (tech, tools, species, religion, nobles, climate), production chain, commute and storage distances.
- **Game exchange (Better Blueprints):** export a layout as a blueprint line and paste it in the game; import blueprint lines, `AreaBlueprints.json` or `SavedPrints` from the game.

Press **Help** in the planner for details, or **Ctrl+K** to search buildings, templates and commands.

## Your data

Plans, templates and settings are stored in your browser (local storage) for this site only. To move them to another browser or device, use **Plan → Save & share → plan code**.

## Updates

New versions are published here. The version is shown in the header (e.g. `v35`); changes are listed in [CHANGELOG.md](CHANGELOG.md).

## Building from source

The page is a single self-contained `index.html`. The parts are in `src/`:

| File | Content |
|---|---|
| `frame.html`, `head.html` | page wrapper, styles, markup |
| `core.js` | room rules and calculations |
| `opt.js` | auto-furnish optimizer |
| `app.js` | user interface |
| `*71.json` | game data for v71 (buildings, extra data, furniture, built-in templates) |

```
cd src
node build.js     # writes ../index.html
```

## Credits

- Room rules, optimizer and the data extraction approach are based on [Syx-Vis](https://github.com/nobody0/syx-vis) by nobody0 (MIT License, notice kept in `core.js` and `opt.js`).
- Blueprint format: the **Better Blueprints** mod for Songs of Syx.
- Game data © Gamatron (Jake). Songs of Syx is made by Gamatron.

**Syx Pack is a fan project and is not affiliated with or endorsed by Gamatron.**

## License

[MIT](LICENSE)
