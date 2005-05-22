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


var urlMainPage = 'https://tisvu.vu.nl/tis/TI_SEC_PCK.TI_LOGON';
var urlLoginRequest = 'https://tisvu.vu.nl/tis/TI_SEC_PCK.TI_CHECK_LOGON';
var urlLogoutRequest = 'https://tisvu.vu.nl/tis/ti_sec_pck.ti_check_logoff';



/***********************************************************************
    Global vars
***********************************************************************/


var pageLoginForm;
var pageIndex;
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
        <li id="linkUitslagen">Tentamen uitslagen</li>\
        <li id="linkLogout">Uitloggen</li>\
    </ul>\
';


var pageLoginFormHTML = '\
    <h2>Inloggen</h2>\
    <form id="formLogin">\
    <input id="user">\
    <input type="password" id="password">\
    <input type="submit" value="login">\
    </form>\
';


var pageIndexHTML = '\
    <h2>Index</h2>\
    <p>Hoi, dit is TisNiks.</p>\
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


function showError(e) {

    document.getElementById('error').innerHTML = e;
    pageError.style.display = '';

}


function hidePages() {

    pageIndex.style.display = 'none';
    pageLoginForm.style.display = 'none';
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

    var req;

    function sendLogin() {

        var str = 'P_USERID=' + name + '&P_PASSWORD=' + password;
        var url = urlLoginRequest;

        if (window.XMLHttpRequest){
            req = new XMLHttpRequest();
        } else {
            showError('Could not make login request.');
            return;
        }

        req.open('POST', url, true);

        req.setRequestHeader('Content-Type',
                             'application/x-www-form-urlencoded; charset=UTF-8');

        req.onreadystatechange = handleLogin;

        req.send(str);

    }

    function handleLogin() {

        // Ready state 4 is 'complete'

        if (req.readyState != 4) return;

        if (req.status == 200) {

            /*
                String 'studieadministratie' is only present in a
                success response.
            */

            if (/studieadministratie/i.test(req.responseText)) {
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

        var url = urlLogoutRequest;

        if (window.XMLHttpRequest){
            req = new XMLHttpRequest();
        } else {
            showError('Could not make logout request.');
            return;
        }

        req.open('GET', url, true);

        req.onreadystatechange = handleLogout;

        req.send(null);

    }

    function handleLogout() {

        // Ready state 4 is 'complete'

        if (req.readyState != 4) return;

        if (req.status == 200) {

            showError('Logged out.');

        } else {

            showError('Could not make logout request.');

        }

    }

    sendLogout();

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

    pageLoginForm = document.createElement('div');
    pageLoginForm.innerHTML = pageLoginFormHTML;
    pageLoginForm.style.display = 'none';

    body.appendChild(pageLoginForm);

    pageIndex = document.createElement('div');
    pageIndex.innerHTML = pageIndexHTML;
    pageIndex.style.display = 'none';

    body.appendChild(pageIndex);

    pageError = document.createElement('div');
    pageError.innerHTML = pageErrorHTML;
    pageError.style.display = 'none';

    body.appendChild(pageError);

    //showLoginForm();
    showIndex();

    // Add event handlers to forms and links

    document.getElementById('formLogin').onsubmit = function() {
        login(document.getElementById('user').value, document.getElementById('password').value); return false;
    };

    document.getElementById('linkIndex').onclick = function() {
        showIndex();
    };

    document.getElementById('linkLogin').onclick = function() {
        showLoginForm();
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
    */

    if (window.location.href == urlMainPage) {

        emptyBody();
        addGlobalStyle(styleSheet);
        createPage();

    } else {

        /*
            This will get us past the frameset (and all other
            pages you might point your browser to).
        */

        window.location.href = urlMainPage;

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

*/
