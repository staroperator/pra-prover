'use strict';
const input = document.querySelector('#search');
const results = document.querySelector('#search-results');
const status = document.querySelector('#search-status');
function search() {
  const query = input.value.trim().toLocaleLowerCase();
  results.replaceChildren();
  if (!query) { status.textContent = ''; return; }
  const matches = window.praDeclarations.filter(row => row[0].toLocaleLowerCase().includes(query));
  matches.sort((a, b) => (a[0].toLocaleLowerCase() !== query) -
    (b[0].toLocaleLowerCase() !== query) || a[0].length - b[0].length);
  status.textContent = `${matches.length} matching declarations` +
    (matches.length > 80 ? ' · showing the first 80' : '');
  for (const [name, page, kind] of matches.slice(0, 80)) {
    const item = document.createElement('li');
    const link = document.createElement('a');
    link.href = `${page}#${encodeURIComponent('d-' + name)}`;
    link.textContent = name;
    const detail = document.createElement('small');
    detail.textContent = kind;
    item.append(link, detail);
    results.append(item);
  }
}
if (input) {
  input.addEventListener('input', search);
  input.value = new URLSearchParams(location.search).get('q') || '';
  search();
}
