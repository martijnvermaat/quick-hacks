<?php


/*
    Class: Adwords
    Provides access to the Google Adwords API v2009.

    Tested with PHP 4.4.9

    2009-11-26
    Martijn Vermaat (martijn@vermaat.name)
*/


class Adwords {


/*
  All class variables supposed to be handled as private to the class.
*/
var $email = '';
var $password = '';
var $client_email = '';
var $developer_token = '';
var $application_token = '';

var $auth_token = null;
var $services = array('AdGroup'   => null,
                      'Criterion' => null);

var $auth_account_type = 'GOOGLE';
var $auth_service = 'adwords';

var $soap_endpoint = 'https://adwords-sandbox.google.com/api/adwords/cm/v200906';
var $soap_wsdl = 'wsdl';

var $namespace = 'https://adwords.google.com/api/adwords/cm/v200909';
var $user_agent = 'PHP4 Adwords API v2009 class';


/*
  Constructor makes no requests. Authentication and Soap client instantiation
  is only done when needed.
*/
function Adwords($email, $password, $client_email, $developer_token,
                 $application_token, $application = '') {

    $this->email = $email;
    $this->password = $password;
    $this->client_email = $client_email;
    $this->developer_token = $developer_token;
    $this->application_token = $application_token;

    if ($application !== '') {
        $this->user_agent = $application.' ('.$this->user_agent.')';
    }

}


function get_all_ad_groups($campaign_id) {

    $auth = $this->__get_auth_token();
    $service = $this->__get_service('AdGroupService');

    $headers =
'<RequestHeader xmlns="' . $this->namespace . '">' .
'<authToken>' . $auth->get_auth_token() . '</authToken>' .
  '<clientEmail>' . $this->client_email . '</clientEmail>' .
  '<userAgent>' . $this->user_agent . '</userAgent>' .
  '<developerToken>' . $this->developer_token . '</developerToken>' .
  '<applicationToken>' . $this->application_token . '</applicationToken>' .
'</RequestHeader>';

    $service->setHeaders($headers);
    $service->soap_defencoding = 'UTF-8';

    $request_xml =
  '<get xmlns="' . $this->namespace . '">' .
  '<selector>' .
  '<campaignId>' . $campaign_id . '</campaignId>' .
  '</selector>' .
'</get>';

    $groups = $service->call('get', $request_xml);
    $groups = $groups['rval']['entries'];

    if ($service->fault) {
        $this->show_fault($service);
        return;
    }

    # Convert to a list if we get back a single object.
    if (!$groups[0]) {
        $groups = array($groups);
    }

    # Display group info.
    for ($i = 0; $i < count($groups); $i++) {
        if ($groups[$i]) {
            echo "\n\n";
            print_r($groups[$i]);
            //echo 'Group status is "' . $groups[$i]['status'] . '" and id is "' .
            //$ads[$i]['ad']['id'] . '".' . "\n";
        }
    }

}


/*
  Get authentication token for Adwords and create it if it does not yet exist.
*/
function __get_auth_token() {

    if ($this->auth_token === null) {

        $this->auth_token =
            $this->__create_auth_token($this->email,
                                       $this->password,
                                       $this->auth_account_type,
                                       $this->auth_service);

    }

    return $this->auth_token;

}


/*
  Get Soap client for an Adwords service and create it if it does not yet
  exist.
*/
function __get_service($service) {

    if ($this->services[$service] === null) {

        $url = $this->soap_endpoint.'/'.$service.'?wsdl';

        $this->services[$service] =
            $this->__create_soap_client($url, $this->soap_wsdl);

    }

    return $this->services[$service];

}


/*
  Create new authentication token.
*/
function __create_auth_token($email, $password, $account_type, $service) {

    return new AuthToken($email, $password, $account_type, $service);

}


/*
  Create new Soap client using the NuSOAP library.
*/
function __create_soap_client($endpoint, $wsdl = false, $proxyhost = false,
                           $proxyport = false, $proxyusername = false,
                           $proxypassword = false, $timeout = 0,
                           $response_timeout = 30) {

    if (!extension_loaded('soap')) {
        return new soapclient($endpoint, $wsdl, $proxyhost, $proxyport,
                              $proxyusername, $proxypassword, $timeout,
                              $response_timeout);
    } else {
        return new nusoap_client($endpoint, $wsdl, $proxyhost, $proxyport,
                                 $proxyusername, $proxypassword, $timeout,
                                 $response_timeout);
    }

}


function show_fault($service) {
  echo "\n";
  echo 'Fault: ' . $service->fault . "\n";
  echo 'Code: ' . $service->faultcode . "\n";
  echo 'String: ' . $service->faultstring . "\n";
  echo 'Detail: ' . $service->faultdetail . "\n";
}


}


/*
function show_xml($service) {
  echo $service->request;
  echo $service->response;
  echo "\n";
}

function show_fault($service) {
  echo "\n";
  echo 'Fault: ' . $service->fault . "\n";
  echo 'Code: ' . $service->faultcode . "\n";
  echo 'String: ' . $service->faultstring . "\n";
  echo 'Detail: ' . $service->faultdetail . "\n";
}
*/

?>
