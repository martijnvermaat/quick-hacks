// ==UserScript==
// @name          TisNiks
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   TisVU enhancer
// @include       https://tisvu.vu.nl/*
// ==/UserScript==


var pageLoginForm;
var pageIndex;


function login(name, password) {

    var req;

    function sendLogin() {

        var str = "P_USERID=" + name + "&P_PASSWORD=" + password;
        var url = "https://tisvu.vu.nl/tis/TI_SEC_PCK.TI_CHECK_LOGON";

        if (window.XMLHttpRequest){
            req = new XMLHttpRequest();
        } else if (window.ActiveXObject) {
            req = new ActiveXObject("Microsoft.XMLHTTP");
        } else {
            return;
        }

        req.open("POST", url, true);

        req.setRequestHeader("Content-Type",
                             "application/x-www-form-urlencoded; charset=UTF-8");

        req.onreadystatechange = handleLogin;

        req.send(str);

    }

    function handleLogin() {

        if (req.readyState != 4) return;

        loginState = (req.status == 200);

    }

    sendLogin();

}


function emptyBody() {

    var body = document.getElementsByTagName('BODY')[0];

    if (body) {
        body.innerHTML = '';
    }

}


function createPage() {

    var body = document.getElementsByTagName('BODY')[0];

    pageLoginForm = document.createElement('form');
    pageLoginForm.innerHTML = '<input name="user"><input type="password" name="password">';
    pageLoginForm.innerHTML += '<a href="#" onclick="alert(\'hoi\')">login</a>';
    pageLoginForm.style.display = 'none';

    body.appendChild(pageLoginForm);

    showIndex();

}


function showLoginForm() {

    pageLoginForm.style.display = '';

}


function showIndex() {

    pageIndex.style.display = '';

}


function tisNiks() {

    if (window.location.href == pageUrl) {

        emptyBody();
        createPage();
        login('mvt600', '');

    } else {

        window.location.href = pageUrl;

    }

}


tisNiks();

/*
Als we bij een request terug krijgen dat we niet ingelogd zijn, dan
laten we pas het login formulier zien.
*/
