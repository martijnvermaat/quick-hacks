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
 * This code sample creates a new keyword given an existing ad group. To create
 * an ad group, you can run add_ad_group.php.
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
$ad_group_criterion_service = SoapClientFactory::GetClient(
  'https://adwords-sandbox.google.com/api/adwords/cm/v200906' .
  '/AdGroupCriterionService?wsdl', 'wsdl');
$ad_group_criterion_service->setHeaders($headers);
$ad_group_criterion_service->soap_defencoding = 'UTF-8';
$debug = 0;

# Create new keyword structure.
$ad_group_id = '5000050779';
$ad_group_criterion_xml =
  '<adGroupId>' . $ad_group_id . '</adGroupId>' .
  '<criterion xsi:type="Keyword">' .
  '<text>maaanlanding</text>' .
  '<matchType>BROAD</matchType>' .
  '</criterion>';

$request_xml =
  '<mutate xmlns="' . $namespace . '">' .
  '<operations>' .
  '<operator>ADD</operator>' .
  '<operand xsi:type="BiddableAdGroupCriterion">' . $ad_group_criterion_xml .
  '</operand>' .
  '</operations>' .
  '</mutate>';

# Add keyword.
$criteria = $ad_group_criterion_service->call('mutate', $request_xml);
$criteria = $criteria['rval']['value'];
if ($debug) {
  show_xml($ad_group_criterion_service);
}
if ($ad_group_criterion_service->fault) {
  show_fault($ad_group_criterion_service);
  exit(1);
}

# Convert to a list if we get back a single object.
if (!$criteria[0]) {
  $criteria = array($criteria);
}

# Display keyword.
for ($i = 0; $i < count($criteria); $i++) {
  echo 'New keyword with text "' . $criteria[$i]['criterion']['text'] .
    '" and id "' . $criteria[$i]['criterion']['id'] . '" was created.' .
    "\n";
}


function show_xml($service) {
  echo $service->request;
  echo $service->response;
  echo "\n";
}

function show_fault($service) {
  echo "\n";
  echo 'Fault: ' . $service->fault . "<br>\n";
  echo 'Code: ' . $service->faultcode . "<br>\n";
  echo 'String: ' . $service->faultstring . "<br>\n";
  echo 'Detail: ' . $service->faultdetail . "<br>\n";
}
