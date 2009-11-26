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

var $soap_endpoint = 'https://adwords-sandbox.google.com/api/adwords/cm/v200909';
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


function get_campaigns($number = 0, $first = 0) {

    $selector = $this->__campaign_selector_ids(array(),
                                               $number,
                                               $first);

    return $this->__get_campaigns($selector);

}


function get_ad_groups_by_campaign($campaign_id, $number = 0, $first = 0) {

    $selector = $this->__ad_group_selector_campaign_id($campaign_id,
                                                       $number,
                                                       $first);

    return $this->__get_ad_groups($selector);

}


function get_criteria_by_ad_group($ad_group_id, $number = 0, $first = 0) {

    $selector = $this->__criteria_selector_ad_group_id($ad_group_id,
                                                       $number,
                                                       $first);

    return $this->__get_criteria($selector);

}


function __get_campaigns($selector) {

    $request = '<get xmlns="'.$this->namespace.'">'.$selector.'</get>';

    return $this->__call_service('CampaignService', $request, 'get');

}


function __get_ad_groups($selector) {

    $request = '<get xmlns="'.$this->namespace.'">'.$selector.'</get>';

    return $this->__call_service('AdGroupService', $request, 'get');

}


function __get_criteria($selector) {

    $request = '<get xmlns="'.$this->namespace.'">'.$selector.'</get>';

    return $this->__call_service('AdGroupCriterionService', $request, 'get');

}


function __campaign_selector_ids($campaign_ids, $number, $first) {

    $paging = $this->__paging($number, $first);

    return '<selector>
              <ids>'.implode(' ', $campaign_ids).'</ids>
              '.$paging.'
            </selector>';

}


function __ad_group_selector_campaign_id($campaign_id, $number, $first) {

    $paging = $this->__paging($number, $first);

    return '<selector>
              <campaignId>'.$campaign_id.'</campaignId>
              '.$paging.'
            </selector>';

}


function __criteria_selector_ad_group_id($ad_group_id, $number, $first) {

    $paging = $this->__paging($number, $first);

    return '<selector>
              <idFilters>
                <adGroupId>'.$ad_group_id.'</adGroupId>
              </idFilters>
              '.$paging.'
            </selector>';

}


function __paging($number, $first) {

    if ($number == 0) {
        return '';
    } else {
        return '<paging>
                  <startIndex>'.$first.'</startIndex>
                  <numberResults>'.$number.'</numberResults>
                </paging>';
    }

}


function __call_service($name, $request, $request_type = 'get') {

    $auth = $this->__get_auth_token();
    $service = $this->__get_service($name);

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

    $response = $service->call($request_type, $request);

    /* TODO
    if ($service->fault) {
        $this->show_fault($service);
        // There is also something in $response['faultcode'] and $response['faultstring']
        return;
    }
    */

    $result = $response['rval'];

    // TODO: move array casting to specific GET handling

    /* Make sure we always return a list of result entries */
    if (!$result['entries'][0]) {
        $result['entries'] = array($result['entries']);
    }

    return $result;

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
