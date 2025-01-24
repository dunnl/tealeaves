const path = require('path');
const fs = require('fs');
const mustache = require('mustache');

// Use __dirname to resolve paths relative to the script's location
const baseDir = __dirname; // Directory where generate.js resides

// Resolve paths using __dirname
const filePath = path.join(baseDir, '../html-alectryon/files.txt'); // Adjust to the correct relative path
const templatePath = path.join(baseDir, '../extra/toc-alectryon.mustache');
const outputPath = path.join(baseDir, '../html-alectryon/toc.html');

// Read the file list
const files = fs.readFileSync(filePath, 'utf8').trim().split('\n');

// Transform the data into a format suitable for Mustache
const data = {
  files: files.map(file => ({
      name: `${file.replace(/\.html$/, '')}`,
      url: `/${file.replace(/\.v$/, '.html')}`
  }))
};

// Read the template
const template = fs.readFileSync(templatePath, 'utf8');

// Render the HTML
const output = mustache.render(template, data);

// Write the output to an HTML file
fs.writeFileSync(outputPath, output);

console.log('HTML file generated:', outputPath);
