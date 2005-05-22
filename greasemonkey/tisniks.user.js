// ==UserScript==
// @name          TisNiks
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   TisVU enhancer
// @include       https://tisvu.vu.nl/*
// ==/UserScript==


var urlMainPage = 'https://tisvu.vu.nl/tis/TI_SEC_PCK.TI_LOGON';
var urlLoginRequest = 'https://tisvu.vu.nl/tis/TI_SEC_PCK.TI_CHECK_LOGON';

var pageLoginForm;
var pageIndex;
var pageError;


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

        if (req.readyState != 4) return;

        if (req.status == 200) {
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


function emptyBody() {

    var body = document.getElementsByTagName('BODY')[0];

    if (body) {
        body.innerHTML = '';
    }

}


var navigationHTML = '\
    <h1>TisNiks</h1>\
    <ul>\
        <li>Index</li>\
        <li>Login</li>\
        <li>Tentamen uitslagen</li>\
        <li>Uitloggen</li>\
    </ul>\
';


var pageLoginFormHTML = '\
    <h2>Inloggen</h2>\
    <form id="loginForm">\
    <input id="user">\
    <input type="password" id="password">\
    <input type="submit" value="login">\
    </form>\
';


var pageIndexHTML = '\
    <h2>Index</h2>\
    <p>index</p>\
';


var pageErrorHTML = '\
    <h2>Fout</h2>\
    <p id="error">undefined</p>\
';


function createPage() {

    var body = document.getElementsByTagName('BODY')[0];

    navigation = document.createElement('div');
    navigation.innerHTML = navigationHTML;

    body.appendChild(navigation);

    pageLoginForm = document.createElement('div');
    pageLoginForm.innerHTML = pageLoginFormHTML;
    pageLoginForm.style.display = 'none';

    body.appendChild(pageLoginForm);

    document.getElementById('loginForm').onsubmit = function() {
        login(document.getElementById('user').value, document.getElementById('password').value); return false;
    };

    pageIndex = document.createElement('div');
    pageIndex.innerHTML = pageIndexHTML;
    pageIndex.style.display = 'none';

    body.appendChild(pageIndex);

    pageError = document.createElement('div');
    pageError.innerHTML = pageErrorHTML;
    pageError.style.display = 'none';

    body.appendChild(pageError);

    showLoginForm();
    //login('hoi','hoi');
    //showIndex();

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


function tisNiks() {

    if (window.location.href == urlMainPage) {

        emptyBody();
        createPage();

    } else {

        window.location.href = urlMainPage;

    }

}


tisNiks();

/*
Als we bij een request terug krijgen dat we niet ingelogd zijn, dan
laten we pas het login formulier zien.
*/
