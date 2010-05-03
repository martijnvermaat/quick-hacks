// ==UserScript==
// @name          Logical Verification Admin Results
// @namespace     http://www.cs.vu.nl/~tcs/lv/
// @description   Add results to Logical Verification admin page
// @include       http://prover.cs.ru.nl/cgi/admin.ml
// @require       http://ajax.googleapis.com/ajax/libs/jquery/1.3.2/jquery.min.js
// ==/UserScript==

/*
  By Martijn Vermaat, martijn@vermaat.name

  Undocumented, ugly, but working.

  To update the icons, run

    ./updatejson < participants.txt > ~/www/lv/results.js

  from the lv directory.
*/

// Load JSON results
(function(){
    if (typeof unsafeWindow.results == 'undefined') {
        var GM_Head = document.getElementsByTagName('head')[0] || document.documentElement,
        GM_JSON = document.createElement('script');

        GM_JSON.src = 'http://www.cs.vu.nl/~tcs/lv/results.js';
        GM_JSON.type = 'text/javascript';
        GM_JSON.async = true;

        GM_Head.insertBefore(GM_JSON, GM_Head.firstChild);
    }
    GM_wait();
})();

// Check if JSON results are loaded
function GM_wait() {
    if (typeof unsafeWindow.results == 'undefined') {
        window.setTimeout(GM_wait, 100);
    } else {
        showResults();
    }
}

// Add result icons to user list
function showResults() {

    var results = unsafeWindow.results;

    $('tr').each(function(i) {
        var login = $(this).find('td').eq(0).text().match(/\(([a-z]+)\)/);
        if (login) {
            for (var i = 0; i < results.length; i++) {
                if (results[i]['name'] == login[1]) {
                    var s = '';
                    for (var j = 0; j < results[i]['results'].length; j++) {
                        switch (results[i]['results'][j]) {
                        case 0:
                            s += '<span class="fail">&#10008;</span>'
                            break;
                        case 1:
                            s += '<span class="pass">&#10004;</span>'
                            break;
                        case 2:
                            s += '<span class="perfect">&#9733;</span>'
                            break;
                        }
                    }
                    $(this).append($('<td class="results"><p>' + s + '</p></td>'));
                    break;
                }
            };
            }
    });

    $('.results').css({'background-color' : '#ccc', 'border' : 'none',
                       'font-size': '16px', 'font-weight' : 'bold'});
    $('.results span').css({'display' : 'inline-block', 'width' :
                            '30px', 'text-align' : 'center'});
    $('.fail').css({'color' : 'red'});
    $('.pass').css({'color' : 'green'});
    $('.perfect').css({'color' : 'yellow'});

}
