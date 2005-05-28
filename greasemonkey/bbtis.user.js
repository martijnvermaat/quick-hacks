// ==UserScript==
// @name          BBTis
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   Blackboard homepage enhanced with latest TisVU results
// @include       http://bb.vu.nl/*
// ==/UserScript==


/*
    BBTis

    Version: 1.0, 2005-05-26


    This is just a quick hack to see what's possible with
    some Greasemonkey magic and TisVU.

    http://www.cs.vu.nl/~mvermaat/tisniks

    Martijn Vermaat, mvermaat@cs.vu.nl


    BBTis is Open Source and licensed under the new BSD
    License, found at:
    http://www.opensource.org/licenses/bsd-license.php
*/



/*
    Wrap the whole thing in an anonymous function to avoid
    nameclashes with existing Javascript.
*/
(function() {



/***********************************************************************
    Configuration
***********************************************************************/


var maxTisResults    = 8;
var autoLogin        = false;
var tisUser          = '';      /* VU-net-id (if autoLogin=true) */
var tisPassword      = '';
var urlMainPage      = 'http://bb.vu.nl/webapps/portal/tab/_1_1/index.jsp';



/***********************************************************************
    Helper functions
***********************************************************************/


function showLoginForm() {

    document.getElementById('tisLogin').style.display = '';

}


function showLoginError() {

    // I admit, this is ugly
    var s = '<b style="color:#c00">Login failed, try again.</b>';

    document.getElementById('tisError').innerHTML = s;

}


function hideLoginError() {

    document.getElementById('tisError').innerHTML = '';

}


/*
    Create a table from the results and put it in place.
*/

function showResults(results) {

    document.getElementById('tisLogin').style.display = 'none';

    var table = document.createElement('table');
    var row;

    table.style.width = '100%';

    // Add some ugly Blackboard HTML for the table header
    table.innerHTML = '<tr><th colspan="3" align="left" bgcolor="#f0f0f0">'
        + '<font face="Arial, Helvetica, sans-serif" size="2">'
        + 'Results from <a href="http://tisvu.vu.nl/">TisVU</a>:</font></th></tr>';

    for (var i = 0; i < results.length && i < maxTisResults; i++) {

        row = document.createElement('tr');

        cell = document.createElement('td');
        cell.appendChild(document.createTextNode(results[i].date));
        row.appendChild(cell);

        cell = document.createElement('td');
        cell.appendChild(document.createTextNode(results[i].course));
        row.appendChild(cell);

        cell = document.createElement('td');
        cell.appendChild(document.createTextNode(results[i].result));
        row.appendChild(cell);

        table.appendChild(row);

    }

    document.getElementById('tisResults').appendChild(table);

}



/***********************************************************************
    TisNiks Library
***********************************************************************/


var tisNiks = {

    /*
        TisNiks is a collection of functions for querying TisVU.

        This version is somewhere near 0.0003 or something.

        http://www.cs.vu.nl/~mvermaat/tisniks
    */


    /*
        Local variables
    */

    tisNiksLog:      false,

    urlLoginRequest: 'https://tisvu.vu.nl/tis/TI_SEC_PCK.TI_CHECK_LOGON',
    urlResults:      'https://tisvu.vu.nl/tis/TI001Q01$TUV.QueryList',
    urlSetCookies:   'https://tisvu.vu.nl/tis/menu',


    /*
        Try to do a login. We show the login form on authorization
        failure, and the index page on success.
    */

    login: function(name, password, onSuccess, onFailure) {

        var log = this.log;
        var url = this.urlLoginRequest;

        /*
            Before trying to login, make a request to TisVU
            that sets some cookies. If we don't have these
            cookies, it won't let us login.
        */

        function doLogin() {
            GM_xmlhttpRequest({
                method:  'POST',
                url:     url,
                data:    'P_USERID=' + name + '&P_PASSWORD=' + password,
                headers: { 'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8' },
                onload:  function(details) {

                    if (details.status == 200) {

                        /*
                            String 'studieadministratie' is only present in a
                            success response.
                        */

                        if (/studieadministratie/i.test(details.responseText)) {
                            log('logged in');
                            onSuccess();
                        } else {
                            log('username/password incorrect');
                            onFailure('authorization');
                        }

                    } else {

                        log('Could not make login request');
                        onFailure('request');

                    }

                }

            });
        }

        this.setCookies(doLogin, (function() {}));

    },


    /*
        Get TisVU results.
    */

    getResults: function(onSuccess, onFailure) {

        var log = this.log;

        GM_xmlhttpRequest({
            method:  'GET',
            url:     this.urlResults,
            onload:  function(details) {

                if (details.status == 200) {

                    if (/geen gegevens verkregen/i.test(details.responseText)) {

                        /*
                            No results means:
                            There just are no results, or we're not logged in.
                        */

                        log('No results found');
                        onFailure('empty');

                    } else {

                        /*
                            This regular expression will give results like this:

                            {
                              code:           545324
                              administration: WI
                              course:         Course Name
                              date:           dd-mm-yyyy
                              result:         9+
                            }
                        */

                        var match;
                        var results = new Array();

                        while (match = /TARGET="fraVF">([^<]+)<\/A><\/TD><TD ALIGN="LEFT">([^<]+)<\/TD><TD ALIGN="LEFT">([^<]+)<\/TD><TD ALIGN="LEFT">([^>]+)<\/TD><TD ALIGN="LEFT">([^>]+)<\/TD>/g.exec(details.responseText)) {
                            results.push({
                                code:           match[1],
                                administration: match[2],
                                course:         match[3],
                                date:           match[4],
                                result:         match[5]
                            });
                        }

                        log('Received results');
                        onSuccess(results);

                    }

                } else {

                    log('Could not make results request');
                    onFailure('request');

                }

            }

        });

    },


    /*
        Request a page on TisVU that sets some cookies.
    */

    setCookies: function(onSuccess, onFailure) {

        var log = this.log;

        GM_xmlhttpRequest({
            method:  'GET',
            url:     this.urlSetCookies,
            onload:  function(details) {

                if (details.status == 200) {

                    log('Made request for cookies');
                    onSuccess();

                } else {

                    log('Could not make request for cookies');
                    onFailure();

                }

            }
        });

    },


    /*
        Log using Greasemonkey logging function.
    */

    log: function(message) {

        if (this.tisNiksLog) {
            GM_log('TisNiks: ' + message);
        }

    }


}



/***********************************************************************
    Main function
***********************************************************************/


/*
    Add the TisVU section, and try to fetch some results.
    Initialize form handlers and stuff.
*/

function bbTis() {

    var divTis = document.createElement('div');
    divTis.style.display = 'none';

    // First match will be the left column of My Blackboard sections
    var tds = document.evaluate(
                            "//td[@width='50%']",
                            document,
                            null,
                            XPathResult.ORDERED_NODE_SNAPSHOT_TYPE,
                            null);

    if (tds.snapshotLength > 0) {
        tds.snapshotItem(0).appendChild(divTis);
    } else {
        return;
    }

    // This is the ugly HTML for our TisVU section
    var s = '<table border="0" bgcolor="336699" cellspacing="0" cellpadding="1" width="100%"><tr><td>'
        + '<table border="0" bgcolor="336699" cellspacing="0" cellpadding="2" width="100%"><tr>'
        + '<td bgcolor="336699" width=5><img src="/images/spacer.gif" width=2></td>'
        + '<td width="100%" bgcolor="336699" ><a name="TisVU"></a><span class="moduleTitle">'
        + '<font color =" FFFFFF">TisVU&nbsp;</font></span></td><td align="right" valign="top" width="1%">'
        + '</td></tr></table><table border="0" cellspacing="0" cellpadding="4" width="100%"><tr>'
        + '<td bgcolor="FFFFFF" class="moduleBody"><FONT size=2><p>'
        + '<form id="tisLogin" style="display:none"><table width="100%">'
        + '<tr><th colspan="2" align="left" bgcolor="#f0f0f0"><font face="Arial, Helvetica, sans-serif" size="2">'
        + 'Please login</font></th></tr>'
        + '<tr><td><label for="tiuser">VU-net-id:</label></td><td><input id="tisuser"></td></tr>'
        + '<tr><td><label for="tispassword">Password:</label></td><td><input type="password" id="tispassword"></td></tr>'
        + '<tr><td></td><td><input type="submit" value="Login"></td></tr></table>'
        + '<div id="tisError"></div></form>'
        + '<div id="tisResults"></div>'
        + '</p></FONT></td></tr></table></td></tr></table><br>';

    divTis.innerHTML = s;

    // Add handler for submit of login form
    document.getElementById('tisLogin').onsubmit = function() {
        hideLoginError();
        tisNiks.login(document.getElementById('tisuser').value,
                      document.getElementById('tispassword').value,
                      (function()  { tisNiks.getResults(showResults, (function(s) {}) ) }),
                      (function(s) { showLoginError() })
                      );
        return false;
    };

    if (autoLogin) {

        // Try to fetch results, on failure do an autologin
        tisNiks.getResults(showResults,
                           (function(s) {
                               tisNiks.login(tisUser,
                                             tisPassword,
                                             (function()  { tisNiks.getResults(showResults, (function (s) {}) ) }),
                                             (function(s) { showLoginForm() } ));
                           }));

    } else {

        // Try to fetch results, on failure show login form
        tisNiks.getResults(showResults, (function(s) { showLoginForm() }) );

    }

    // Okay, everything is setup, show the thing
    divTis.style.display = '';

}



/***********************************************************************
    Invocation
***********************************************************************/


if (window.location.href == urlMainPage) {
    bbTis();
}


/*
    End of wrapper function (see top of script).
*/
})();
