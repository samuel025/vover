// Copies the browser export library from node_modules into public/vendor.
// Only needed when updating the library: npm install, then npm run vendor.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = path.join(path.dirname(fileURLToPath(import.meta.url)), '..');
const from = path.join(root, 'node_modules', 'mediabunny');
const to = path.join(root, 'public', 'vendor');
fs.mkdirSync(to, { recursive: true });
fs.copyFileSync(path.join(from, 'dist', 'bundles', 'mediabunny.min.mjs'), path.join(to, 'mediabunny.mjs'));
fs.copyFileSync(path.join(from, 'LICENSE'), path.join(to, 'mediabunny.LICENSE'));
console.log('Copied mediabunny to public/vendor');
