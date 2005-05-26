// ==UserScript==
// @name          BBTis
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   Blackboard enhanced with TisVU results
// @include       http://bb.vu.nl/*
// ==/UserScript==


/*
    This is just a quick hack to see what's possible with
    some Greasemonkey magic and TisVU.

    Martijn Vermaat, mvermaat@cs.vu.nl
*/



/***********************************************************************
    Configuration
***********************************************************************/


var applicationTitle = 'TisNiks';

var maxTisResults = 8;

var urlMainPage = 'http://bb.vu.nl/webapps/portal/tab/_1_1/index.jsp';
var urlLoginRequest = 'https://tisvu.vu.nl/tis/TI_SEC_PCK.TI_CHECK_LOGON';
var urlResults = 'https://tisvu.vu.nl/tis/TI001Q01$TUV.QueryList';
var urlSetCookies = 'https://tisvu.vu.nl/tis/menu';



/***********************************************************************
    Helper functions
***********************************************************************/


function showLoginForm() {

    document.getElementById('tisLogin').style.display = '';

}


function showResults(results) {

    document.getElementById('tisLogin').style.display = 'none';

    var table = document.createElement('table');
    var row;

    table.style.width = '100%';

    for (var i = 0; i < results.length && i < maxTisResults; i++) {

        row = document.createElement('tr');

        for (var j = 2; j < results[i].length; j++) {

            if (j == 4) continue;

            cell = document.createElement('td');
            cell.appendChild(document.createTextNode(results[i][j]));
            row.appendChild(cell);

        }

        table.appendChild(row);

    }

    document.getElementById('tisResults').appendChild(table);

}



/***********************************************************************
    Data request functions
***********************************************************************/


/*
    Try to do a login. We show the login form on authorization
    failure, and the index page on success.
*/

function loginAndGetResults(name, password) {

    function sendLogin() {

        GM_xmlhttpRequest({
            method:  'POST',
            url:     urlLoginRequest,
            data:    'P_USERID=' + name + '&P_PASSWORD=' + password,
            headers: {
                'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8'
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
                //showIndex();
                GM_log('logged in');
                getResults();
            } else {
                //showLoginForm();
                //showError('Username/password incorrect.');
                GM_log('username/password incorrect');
            }

        } else {

            GM_log('Could not make login request');

        }

    }

    sendLogin();

}


/*
  Get exam results.
*/

function getResults() {

    function sendResults() {

        GM_xmlhttpRequest({
            method:  'GET',
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

                GM_log('No results found');
                showLoginForm();

                /*
                    Let stupid TisVU set some cookies we need before
                    it lets us login...
                */
                setCookies();

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
                    results.push(match);
                }

                showResults(results);

            }

        } else {

            GM_log('Could not make results request');

        }

    }

    sendResults();

}


/*
    Request a page on TisVU that sets some cookies.
*/

function setCookies() {

    GM_xmlhttpRequest({
        method:  'GET',
        url:     urlSetCookies,
    });

}



/***********************************************************************
    Main functions
***********************************************************************/


/*
    Add our navigation HTML, and build all pages but make
    them invisible for now.
*/

function createPage() {

    var divTis = document.createElement('div');
    divTis.style.display = 'none';

    var tds = document.evaluate(
                            "//td[@width='50%']",
                            document,
                            null,
                            XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE,
                            null);

    if (tds.snapshotLength > 0) {
        tds.snapshotItem(0).appendChild(divTis);
    } else {
        return;
    }

    var extra = '<table border="0" bgcolor="336699" cellspacing="0" cellpadding="1" width="100%"><tr><td>';
    extra += '<table border="0" bgcolor="336699" cellspacing="0" cellpadding="2" width="100%"><tr>';
    extra += '<td bgcolor="336699" width=5><img src="/images/spacer.gif" width=2></td>';
    extra += '<td width="100%" bgcolor="336699" ><a name="TisVU"></a><span class="moduleTitle">';
    extra += '<font color =" FFFFFF">TisVU&nbsp;</font></span></td><td align="right" valign="top" width="1%">';
    extra += '</td></tr></table><table border="0" cellspacing="0" cellpadding="4" width="100%"><tr>';
    extra += '<td bgcolor="FFFFFF" class="moduleBody"><FONT size=2><p>';
    extra += 'Your latest results from <a href="http://tisvu.vu.nl">TisVU</a>:';
    extra += '<form id="tisLogin" style="display:none"><input id="tisuser"><input type="password" id="tispassword">';
    extra += '<input type="submit" value="login"></form>';
    extra += '<div id="tisResults"></div>';
    extra += '</p></FONT></td></tr></table></td></tr></table><br>';

    divTis.innerHTML = extra;

    document.getElementById('tisLogin').onsubmit = function() {
        loginAndGetResults(document.getElementById('tisuser').value,
                           document.getElementById('tispassword').value);
        return false;
    };

    getResults();

    divTis.style.display = '';

}


/*
    Invocation function
*/

function tisNiks() {

    if (window.location.href == urlMainPage) {

        /*
            Eventueel eerst even deze pagina opvragen, zodat
            cookies geset worden door TisVU:
            https://tisvu.vu.nl/tis/menu
        */

        createPage();

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
    Comming soon. A lot of my documentation is in the TisNiks
    userscript.
*/
