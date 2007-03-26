// ==UserScript==
// @name          WideMX
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   Fix for WideXS MX record editor
// @include       https://www.widexs.nl/*
// ==/UserScript==


/*
    WideMX

    Version: 0.1, 2007-03-26

    http://www.cs.vu.nl/~mvermaat/greasemonkey

    Martijn Vermaat, mvermaat@cs.vu.nl


    WideXS provide a DNS record editor form on their website,
    but the maxlength attribute of the MX record value is set
    to a value of 50 characters (which is too short).

    WideMX rewrites this value to 200 characters.


    Nu Compact is Open Source and licensed under the new
    BSD License, found at:
    http://www.opensource.org/licenses/bsd-license.php
*/


(function() {

    function widemx () {

        var nodes, node;
        nodes = document.evaluate("//input[@name='ip']",
                              document,
                              null,
                              XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE,
                              null);

        for (var i = 0; i < nodes.snapshotLength; i++) {
            node = nodes.snapshotItem(i);
            node.setAttribute('maxlength', '200');
        }

    }

    widemx();

})();
