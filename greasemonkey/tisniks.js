/***********************************************************************

    TisNiks

    0.2, 2005-06-04
    Martijn Vermaat, mvermaat@cs.vu.nl
    http://www.cs.vu.nl/~mvermaat/tisniks


    TisNiks is a collection of functions for querying the TisVU
    information system of the Vrije Universiteit Amsterdam.

    It is to be used by Greasemonkey user scripts. TisNiks uses
    features specific to Greasemonkey.


    TisNiks is Open Source and licensed under the new BSD
    License, found at:
    http://www.opensource.org/licenses/bsd-license.php

***********************************************************************/



/***********************************************************************

    Available functions

    ********************************************************************

    tisNiks.login(name, password, onSuccess, onFailure)

        name:      string
        password:  string
        onSuccess: function ()
        onFailure: function (status:string)

    Try to login using name and password. On success, the onSuccess
    function is called. On failure, the onFailure function is called
    with parameters:

        status: Can be 'request' or 'authorization'

    ********************************************************************

    tisNiks.logout(onSuccess, onFailure)

        onSuccess: function ()
        onFailure: function ()

    Try to logout. This should always succeed, logged in or not. On
    success the onSuccess function is called. On failure, the
    onFailure function is called.

    ********************************************************************

    tisNiks.getResults(onSuccess, onFailure)

        onSuccess: function (results:array)
        onFailure: function (status:string)

    Try to fetch exam results. On success, the onSuccess function is
    called with parameters:

        results: An array containing structures of the form

                 { code:           545324
                   administration: WI
                   course:         Course Name
                   date:           dd-mm-yyyy
                   result:         9+ }

    On failure, the onFailure function is called with parameters:

        status: Can be 'request' or 'empty'

    A call of onFailure('empty') means no results were found. This
    can mean you're not logged in or you just have no results. There
    is no way to differentiate between the two.

    ********************************************************************

    tisNiks.getExams(onSuccess, onFailure)

        onSuccess: function (results:array)
        onFailure: function (status:string)

    Try to fetch enrolled exams. On success, the onSuccess function
    is called with parameters:

        results: An array containing structures of the form

                 { code:           545324
                   administration: WI
                   course:         Course Name
                   date:           dd-mm-yyyy }

    On failure, the onFailure function is called with parameters:

        status: Can be 'request' or 'empty'

    A call of onFailure('empty') means no exams were found. This can
    mean you're not logged in or you just have no exams. There is no
    way to differentiate between the two.

***********************************************************************/



var tisNiks = {


    /*
        Local variables
    */

    tisNiksLog:       false,

    urlLoginRequest:  'https://tisvu.vu.nl/tis/TI_SEC_PCK.TI_CHECK_LOGON',
    urlLogoutRequest: 'https://tisvu.vu.nl/tis/ti_sec_pck.ti_check_logoff',
    urlResults:       'https://tisvu.vu.nl/tis/TI001Q01$TUV.QueryList',
    urlExams:         'https://tisvu.vu.nl/tis/TI002M01$TKV.QueryList',
    urlSetCookies:    'https://tisvu.vu.nl/tis/menu',


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
        Do a logout. Simply sending the request should do the trick.
    */

    logout: function (onSuccess, onFailure) {

        var log = this.log;

        GM_xmlhttpRequest({
            method:  'GET',
            url:     this.urlLogoutRequest,
            onload:  function (details) {

                if (details.status == 200) {

                    if (/uitloggen gelukt/i.test(details.responseText)) {

                        log('Logged out');
                        onSuccess();

                    } else {

                        log('Logout failed');
                        onFailure();

                    }

                } else {

                    log('Could not make logout request');
                    onFailure();

                }

            }

        });

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
        Get TisVU exams.
    */

    getExams: function(onSuccess, onFailure) {

        var log = this.log;

        GM_xmlhttpRequest({
            method:  'GET',
            url:     this.urlExams,
            onload:  function(details) {

                if (details.status == 200) {

                    if (/geen gegevens verkregen/i.test(details.responseText)) {

                        /*
                            No exams means:
                            There just are no exams, or we're not logged in.
                        */

                        log('No exams found');
                        onFailure('empty');

                    } else {

                        /*
                            This regular expression will give results like this:

                            {
                              code:           545324
                              administration: WI
                              course:         Course Name
                              date:           dd-mm-yyyy
                            }
                        */

                        var match;
                        var exams = new Array();

                        while (match = /TARGET="fraVF">([^<]+)<\/A><\/TD><TD ALIGN="LEFT">([^<]+)<\/TD><TD ALIGN="LEFT">([^<]+)<\/TD><TD ALIGN="LEFT">([^>]+)<\/TD>/g.exec(details.responseText)) {
                            exams.push({
                                code:           match[1],
                                administration: match[2],
                                course:         match[3],
                                date:           match[4]
                            });
                        }

                        log('Received exams');
                        onSuccess(exams);

                    }

                } else {

                    log('Could not make exams request');
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
