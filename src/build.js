// Builds ../index.html from the parts in this folder.
// Usage (in src/): node build.js
// frame.html = page wrapper (doctype, viewport, base styles); head.html = title, styles and markup;
// *.json = game data for Songs of Syx v71; core.js + opt.js + app.js = code.
const fs = require('fs');
const rd = f => fs.readFileSync(__dirname + '/' + f, 'utf8');
const frame = rd('frame.html'), head = rd('head.html'), app = rd('app.js'), core = rd('core.js') + rd('opt.js');
const bd = rd('bdata71.json'), xd = rd('xdata71.json'), fd = rd('fdata71.json'), td = rd('tdata71.json');
if ([bd, xd, fd, td].some(x => x.includes('</')) || app.includes('</script') || core.includes('</script')) throw new Error('unsafe');
[bd, xd, fd, td].forEach(x => JSON.parse(x));
new Function(core + app);
const page = head + '\n<script id="bdata" type="application/json">' + bd + '</script>\n<script id="xdata" type="application/json">' + xd + '</script>\n<script id="fdata" type="application/json">' + fd + '</script>\n<script id="tdata" type="application/json">' + td + '</script>\n<script>\n' + core + app + '</script>\n';
fs.writeFileSync(__dirname + '/../index.html', frame + page + '</body></html>');
console.log('built index.html', fs.statSync(__dirname + '/../index.html').size, 'bytes');
