// ==UserScript==
// @name          Ad Tweakers
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   Do some ad tweaking on Tweakers.net and GoT
// @include       http://tweakers.net/*
// @include       http://*.tweakers.net/*
// ==/UserScript==


/*
    Ad Tweakers

    Version: 0.1, 2005-05-29

    Martijn Vermaat, mvermaat@cs.vu.nl


    Do some ad tweaking on Tweakers.net and GoT

    Although this script is easy to install, adding the
    following rules to your userContent.css file works
    better because these rules are applied before the
    page is rendered. Drawback is that these rules are
    applied on all websites, not only Tweakers.net.

        #b_468_bg,
        #b_sky,
        #msnbar_holder,
        #textad_holder,
        #advertorial,
        #mainbanner { display : none ! important; }

    This user script still shows ads until rendering the
    page is finished.


    Ad Tweakers is Open Source and licensed under the new
    BSD License, found at:
    http://www.opensource.org/licenses/bsd-license.php
*/



/*
    Wrap the whole thing in an anonymous function to avoid
    nameclashes with existing Javascript.
*/
(function() {


function tweakAds() {

    var elements = ['b_468_bg', 'b_sky', 'msnbar_holder', 'textad_holder', 'advertorial', 'mainbanner', 'bigad_holder'];

    for (var i = 0; i < elements.length; i++) {
        removeElementById(elements[i]);
    }

    var iframes = document.getElementsByTagName('iframe');

    for (var i = 0; i < iframes.length; i++) {
        removeElement(iframes[i]);
    }

}


function removeElementById(id) {

    var element;

    if (element = document.getElementById(id)) {
        removeElement(element);
    }

}


function removeElement(element) {

    element.parentNode.removeChild(element);

}


tweakAds();


/*
    End of wrapper function (see top of script).
*/
})();
