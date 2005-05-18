// ==UserScript==
// @name          Nu.nl test
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   Testen van meta tags
// @include       *
// ==/UserScript==

var adSidebar = document.getElementById('test');
if (adSidebar) {
    adSidebar.parentNode.removeChild(adSidebar);
}
