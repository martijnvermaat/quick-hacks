// ==UserScript==
// @name          TisNiks
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   TisVU enhancer
// @include       https://tisvu.vu.nl/*
// ==/UserScript==


/*
    This is just a quick hack to see what's possible with
    some Greasemonkey magic and Tisvu.

    Martijn Vermaat, mvermaat@cs.vu.nl
*/



/***********************************************************************
    Configuration
***********************************************************************/


var applicationTitle = 'TisNiks';

var urlMainPage = 'https://tisvu.vu.nl/tis/TI_SEC_PCK.TI_LOGON';
var urlLoginRequest = 'https://tisvu.vu.nl/tis/TI_SEC_PCK.TI_CHECK_LOGON';
var urlLogoutRequest = 'https://tisvu.vu.nl/tis/ti_sec_pck.ti_check_logoff';
var urlResults = 'https://tisvu.vu.nl/tis/TI001Q01$TUV.QueryList';



/***********************************************************************
    Global vars
***********************************************************************/


var pageLoginForm;
var pageIndex;
var pageResults;
var pageError;



/***********************************************************************
    CSS style sheet
***********************************************************************/


// No beauty-queen

var styleSheet = '\
html {\
    font-family         :   \'Lucida Grande\', Verdana, Geneva, Lucida, Helvetica, sans-serif;\
    background          :   #6383ab;\
    color               :   #fff;\
    font-size           :   0.8em;\
}\
h1 {\
    background          :   #fffef9;\
    color               :   #334465;\
}\
.nav {\
    list-style-type     :   none;\
    text-align          :   center;\
}\
.nav li {\
    display             :   inline;\
    margin-left         :   2em;\
    font-weight         :   bold;\
    cursor              :   pointer;\
}\
.nav li:hover {\
    color               :   #334465;\
}\
#error {\
    background          :   #fff;\
    color               :   #d33;\
    font-weight         :   bold;\
}\
';



/***********************************************************************
    HTML codes
***********************************************************************/


var navigationHTML = '\
    <h1>TisNiks</h1>\
    <ul class="nav">\
        <li id="linkIndex">Index</li>\
        <li id="linkLogin">Login</li>\
        <li id="linkResults">Results</li>\
        <li id="linkLogout">Logout</li>\
    </ul>\
';


var pageLoginFormHTML = '\
    <h2>Login</h2>\
    <form id="formLogin">\
    <input id="user">\
    <input type="password" id="password">\
    <input type="submit" value="login">\
    </form>\
';


var pageIndexHTML = '\
    <h2>Index</h2>\
    <p>Hi, this is TisNiks.</p>\
';


var pageResultsHTML = '\
    <h2>Results</h2>\
';


var pageErrorHTML = '\
    <p id="error">undefined</p>\
';



/***********************************************************************
    Helper functions
***********************************************************************/


function addGlobalStyle(css) {

    /* Taken from Dive Into Greasemonkey. */

    var head, style;
    head = document.getElementsByTagName('head')[0];
    if (!head) { return; }
    style = document.createElement('style');
    style.type = 'text/css';
    style.innerHTML = css;
    head.appendChild(style);

}


function setPageTitle(title) {

    document.title = title;

}


function setCookies() {

    function setCookie(name, value) {

        document.cookie = name + '=' + value + '; expires=; path=/';

    }

    /*
        Set these two cookies, or TisVu will not let
        us login.
    */

    setCookie('CHECK_COOKIE', 'X');
    setCookie('AUTH_METHOD', 'TIS');

}


function emptyBody() {

    /*
        Empty entire body. We need to get rid of some
        coloring tags too, because they disturbed our
        stylesheet.
    */

    var body = document.getElementsByTagName('BODY')[0];

    if (body) {
        body.innerHTML = '';
        body.setAttribute('BGCOLOR', '');
        body.setAttribute('LINK', '');
        body.setAttribute('VLINK', '');
        body.setAttribute('ALINK', '');
    }

}


function showLoginForm() {

    hidePages();
    pageLoginForm.style.display = '';

}


function showIndex() {

    hidePages();
    pageIndex.style.display = '';

}


function showResults(results) {

    var table = document.createElement('table');
    var row;

    for (var i = 0; i < results.length; i++) {

        row = document.createElement('tr');

        for (var j = 1; j < results[i].length; j++) {

            cell = document.createElement('td');
            cell.appendChild(document.createTextNode(results[i][j]));
            row.appendChild(cell);

        }

        table.appendChild(row);

    }

    pageResults.appendChild(table);

    hidePages();
    pageResults.style.display = '';

}


function showError(e) {

    document.getElementById('error').innerHTML = e;
    pageError.style.display = '';

}


function hidePages() {

    pageIndex.style.display = 'none';
    pageLoginForm.style.display = 'none';
    pageResults.style.display = 'none';
    pageError.style.display = 'none';

}



/***********************************************************************
    Data request functions
***********************************************************************/


/*
    Try to do a login. We show the login form on authorization
    failure, and the index page on success.
*/

function login(name, password) {

    function sendLogin() {

        GM_xmlhttpRequest({
            method:  "POST",
            url:     urlLoginRequest,
            data:    'P_USERID=' + name + '&P_PASSWORD=' + password,
            headers: {
                "Content-Type":'application/x-www-form-urlencoded; charset=UTF-8'
                    },
            onload:  handleLogin
        });

    }

    function handleLogin(details) {

        if (details.status == 200) {

            /*
                String 'studieadministratie' is only present in a
                success response.
            */

            if (/studieadministratie/i.test(details.responseText)) {
                showIndex();
            } else {
                showLoginForm();
                showError('Username/password incorrect.');
            }

        } else {

            showError('Could not make login request.');

        }

    }

    sendLogin();

}


/*
    Do a logout. Simply sending the request should do the trick.
*/

function logout() {

    function sendLogout() {

        GM_xmlhttpRequest({
            method:  "GET",
            url:     urlLogoutRequest,
            onload:  handleLogout
        });

    }

    function handleLogout(details) {

        if (details.status == 200) {

            if (/uitloggen gelukt/i.test(details.responseText)) {
                showError('Logged out.');
            } else {
                showError('Logout failed.');
            }

        } else {

            showError('Could not make logout request.');

        }

    }

    sendLogout();

}


/*
  Get exam results.
*/

function getResults() {

    function sendResults() {

        GM_xmlhttpRequest({
            method:  "GET",
            url:     urlResults,
            onload:  handleResults
        });

    }

    function handleResults(details) {

        if (details.status == 200) {

            if (/geen gegevens verkregen/i.test(details.responseText)) {

                /*
                    No results means:
                    There just are no results, or we're not logged in.
                */

                showError('No results found.');

            } else {

                /*
                    This regular expression will give results like this:
                    1 - vakcode
                    2 - administratie
                    3 - vaknaam
                    4 - datum (dd-mm-yyyy format, but we should not depend on that!)
                    5 - cijfer
                */

                var match;
                var results = new Array();

                while (match = /TARGET="fraVF">([^<]+)<\/A><\/TD><TD ALIGN="LEFT">([^<]+)<\/TD><TD ALIGN="LEFT">([^<]+)<\/TD><TD ALIGN="LEFT">([^>]+)<\/TD><TD ALIGN="LEFT">([^>]+)<\/TD>/g.exec(details.responseText)) {
                    //GM_log(match[1] + ", " + match[2] + ", " + match[3] + ", " + match[4] + ", " + match[5]);
                    results.push(match);
                }

                showResults(results);

            }

        } else {

            showError('Could not make results request.');

        }

    }

    sendResults();

}



/***********************************************************************
    Main functions
***********************************************************************/


/*
    Add our navigation HTML, and build all pages but make
    them invisible for now.
*/

function createPage() {

    var body = document.getElementsByTagName('BODY')[0];

    navigation = document.createElement('div');
    navigation.innerHTML = navigationHTML;

    body.appendChild(navigation);

    pageError = document.createElement('div');
    pageError.innerHTML = pageErrorHTML;
    pageError.style.display = 'none';

    body.appendChild(pageError);

    pageLoginForm = document.createElement('div');
    pageLoginForm.innerHTML = pageLoginFormHTML;
    pageLoginForm.style.display = 'none';

    body.appendChild(pageLoginForm);

    pageIndex = document.createElement('div');
    pageIndex.innerHTML = pageIndexHTML;
    pageIndex.style.display = 'none';

    body.appendChild(pageIndex);

    pageResults = document.createElement('div');
    pageResults.innerHTML = pageResultsHTML;
    pageResults.style.display = 'none';

    body.appendChild(pageResults);

    //showLoginForm();
    showIndex();
    //login('vunetid', 'password');

    // Add event handlers to forms and links

    document.getElementById('formLogin').onsubmit = function() {
        login(document.getElementById('user').value, document.getElementById('password').value); return false;
    };

    document.getElementById('linkLogin').onclick = function() {
        showLoginForm();
    };

    document.getElementById('linkIndex').onclick = function() {
        showIndex();
    };

    document.getElementById('linkResults').onclick = function() {
        getResults();
    };

    document.getElementById('linkLogout').onclick = function() {
        logout();
    };

}


/*
    Invocation function
*/

function tisNiks() {

    /*
        We use the TisVU login page as a placeholder. Empty
        the entire page, and build our own in it.

        Just deleting the entire page (not only body) results
        in a crashing Firefox, and so does removing the
        frameset. Therefore, we have to get past the frameset
        and use a 'normal' page and empty only the body.

        We also need to set some cookies (normally set by
        some page in the frameset), otherwise we can't login.
    */

    if (window.location.href == urlMainPage) {

        setCookies();
        emptyBody();
        setPageTitle(applicationTitle);
        addGlobalStyle(styleSheet);
        createPage();

    } else {

        /*
            This will get us past the frameset (and all other
            pages you might point your browser to).
        */

        window.location.replace(urlMainPage);

    }

}



/***********************************************************************
    Invocation
***********************************************************************/


tisNiks();



/***********************************************************************
    Documentation
***********************************************************************/


/*

Authorization

    It is difficult to check if we are logged in or not, so we will
    try to do so. Instead, all functionality is always available, but
    real information can of course only be showed once logged in.

    The user wil have to decide to login, and has to click the login
    link itself.

    Luckily, checking if actual logging in fails or not works, so we
    give feedback on that of course.


Pages

    Every page is contained in a <div> which is set to be invisible
    by default. Only the active page is visible. So, for example,
    after clicking the login link, all page <div>s will be made
    invisible, and then the login form <div> will be made visible.

    Only exception is showing an error message. This will just set
    the error message to be visible, but leave a possible other page
    also visible.


Robusteness

    Yes, this will all break horribly if the TisVU system is changed
    in any way.


Multi-line strings

    The \ continuations are ugly, I know. Know a better way to use
    multi-line strings in Javascript?


XMLHttpRequest

    No need to check here for other browsers' XMLHttpRequest
    implementation, as this script is Firefox only anyway.

    We could add some support for some sort of progress bar here.
    Just update the bar on all ready states instead of only taking
    action on ready state 4.


Known bugs

    Greasemonkey logs an exception to the JavaScript Console upon
    loading our script, but it's as yet unclear why.

      Greasemonkey: http://www.cs.vu.nl/~mvermaat//TisNiks:
      Exception when injecting : {}

*/
