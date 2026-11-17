var hljs = require('highlight.js');
var hljsDefineSolidity = require('highlightjs-solidity');

hljsDefineSolidity(hljs);
// mdBook's scripts access the highlighter through this global.
window.hljs = hljs;
hljs.initHighlightingOnLoad();
