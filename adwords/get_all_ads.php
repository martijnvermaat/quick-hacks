<?php
// Copyright 2009, Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/**
 * This code sample retrieves all ads given an existing ad group. To add
 * ads to an existing ad group, you can run add_text_ad.php.
 */

require_once('AuthToken.php');
require_once('SoapClientFactory.php');

# Provide AdWords login information.
$email = 'adwords@drogisterij.net';
$password = '';
#$client_email = 'testgoogle@drogisterij.net';
$client_email = 'client_1+adwords@drogisterij.net';
$user_agent = 'Drogisterij.net: AdWords API PHP Sample Code';
$developer_token = 'adwords@drogisterij.net++EUR';
$application_token = 'INSERT_APPLICATION_TOKEN_HERE';
$account_type = 'GOOGLE';
$service = 'adwords';

$namespace = 'https://adwords.google.com/api/adwords/cm/v200906';

# Define SOAP headers.
$auth = new AuthToken($email, $password, $account_type, $service);
$headers =
  '<RequestHeader xmlns="' . $namespace . '">' .
  '<authToken>' . $auth->get_auth_token() . '</authToken>' .
  '<clientEmail>' . $client_email . '</clientEmail>' .
  '<userAgent>' . $user_agent . '</userAgent>' .
  '<developerToken>' . $developer_token . '</developerToken>' .
  '<applicationToken>' . $application_token . '</applicationToken>' .
  '</RequestHeader>';

# Set up service connection. To view XML request/response, change value of
# $debug to 1. To send requests to production environment, replace
# "adwords-sandbox.google.com" with "adwords.google.com".
$ad_group_ad_service = SoapClientFactory::GetClient(
  'https://adwords-sandbox.google.com/api/adwords/cm/v200906' .
  '/AdGroupAdService?wsdl', 'wsdl');
$ad_group_ad_service->setHeaders($headers);
$ad_group_ad_service->soap_defencoding = 'UTF-8';
$debug = 0;

# Get all ads.
$ad_group_id = 'INSERT_AD_GROUP_ID_HERE';
$request_xml =
  '<get xmlns="' . $namespace . '">' .
  '<selector>' .
  '<adGroupIds>' . $ad_group_id . '</adGroupIds>' .
  '</selector>' .
  '</get>';
$ads = $ad_group_ad_service->call('get', $request_xml);
$ads = $ads['rval']['entries'];
if ($debug) {
  show_xml($ad_group_ad_service);
}
if ($ad_group_ad_service->fault) {
  show_fault($ad_group_ad_service);
  exit(1);
}

# Convert to a list if we get back a single object.
if (!$ads[0]) {
  $ads = array($ads);
}

# Display ad info.
for ($i = 0; $i < count($ads); $i++) {
  if ($ads[$i]) {
    echo 'Ad status is "' . $ads[$i]['status'] . '" and id is "' .
      $ads[$i]['ad']['id'] . '".' . "\n";
  }
}


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
