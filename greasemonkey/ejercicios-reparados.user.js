// ==UserScript==
// @name          Ejercicios Reparados
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   Fix for Ejercicios de vocabulario
// @include       http://www.let.uu.nl/~Kristi.JauregiOndarra/personal/Tv1/voc*
// ==/UserScript==


/*
    Ejercicios Reparados

    Version: 0.1.1, 2005-10-02


    Fixes 'Ejercicios de vocabulario' on the website of Kristi
    Jauregi Ondarra so that they actually work in Firefox. The
    exercises are by Silvia Canto and located at:
    http://www.let.uu.nl/~Kristi.JauregiOndarra/personal/Tv1/ejervoc.htm

    http://www.cs.vu.nl/~mvermaat/greasemonkey

    Martijn Vermaat, mvermaat@cs.vu.nl


    Ejercicios Reparados is Open Source and licensed under the
    new BSD License, found at:
    http://www.opensource.org/licenses/bsd-license.php


    Changelog

    2005-10-02 - 0.1.1
    * Adjusted include url (removed dot at end)

    2005-10-01 - 0.1
    * Initial version
*/


// Original window.onload calls some non-existing functions

window.onload = function () {};


// Original checkAll function uses document.all

window.checkAll = function () {

    var nodes, node;
    var correctCount = 0;
    var wrongCount = 0;

    // Find all solution text fields
    nodes = document.evaluate("//input[@solution]",
                              document,
                              null,
                              XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE,
                              null);

    for (var i = 0; i < nodes.snapshotLength; i++) {

        node = nodes.snapshotItem(i);

        if (node.value != node.getAttribute('solution')) {
            node.style.backgroundColor = inputErrorColor;
            wrongCount++;
        } else {
            node.style.backgroundColor = inputCorrectColor;
            correctCount++;
        }	

        document.getElementById('correct').firstChild.nodeValue = correctCount;
        document.getElementById('wrong').firstChild.nodeValue = wrongCount;

    }

}


// Original clearAll function uses document.all

window.clearall = function () {

    var nodes, node;

    // Find all solution text fields
    nodes = document.evaluate("//input[@solution]",
                              document,
                              null,
                              XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE,
                              null);

    for (var i = 0; i < nodes.snapshotLength; i++) {

        node = nodes.snapshotItem(i);

        node.value = '';
        node.style.backgroundColor = '#FFFFFF';

    }

    document.getElementById('correct').firstChild.nodeValue = 0;
    document.getElementById('wrong').firstChild.nodeValue = 0;

}


// Original correct function uses document.all

window.correct = function () {

    var nodes, node;

    // Find all solution text fields
    nodes = document.evaluate("//input[@solution]",
                              document,
                              null,
                              XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE,
                              null);

    for (var i = 0; i < nodes.snapshotLength; i++) {

        node = nodes.snapshotItem(i);

        if (node.value != node.getAttribute('solution')) {

            if (node.value == '') {
                node.value = node.getAttribute('solution');
            } else {
                node.value = node.getAttribute('solution') + ' > ' + node.value;
            }

        }	

    }

}
