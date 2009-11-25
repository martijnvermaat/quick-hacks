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

/** This code sample creates a new campaign. */

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
$campaign_service = SoapClientFactory::GetClient(
  'https://adwords-sandbox.google.com/api/adwords/cm/v200906' .
  '/CampaignService?wsdl', 'wsdl');
$campaign_service->setHeaders($headers);
$campaign_service->soap_defencoding = 'UTF-8';
$debug = 0;

# Create new campaign structure.
$campaign_xml =
  '<endDate>20101001</endDate>' .
  '<name>Martijn Campaign - ' . time() . '</name>' .
  '<status>PAUSED</status>' .
  '<biddingStrategy xsi:type="ManualCPC"/>' .
  '<budget>' .
  '<period>DAILY</period>' .
  '<amount>' .
  '<currencyCode>USD</currencyCode>' .
  '<microAmount>1000000</microAmount>' .
  '</amount>' .
  '<deliveryMethod>STANDARD</deliveryMethod>' .
  '</budget>';

$request_xml =
  '<mutate xmlns="' . $namespace . '">' .
  '<operations>' .
  '<operator>ADD</operator>' .
  '<operand>' . $campaign_xml . '</operand>' .
  '</operations>' .
  '</mutate>';

# Add campaign.
$campaigns = $campaign_service->call('mutate', $request_xml);
$campaigns = $campaigns['rval']['value'];
if ($debug) {
  show_xml($campaign_service);
}
if ($campaign_service->fault) {
  show_fault($campaign_service);
  exit(1);
}

# Convert to a list if we get back a single object.
if (!$campaigns[0]) {
  $campaigns = array($campaigns);
}

# Display new campaign.
for ($i = 0; $i < count($campaigns); $i++) {
  echo 'New campaign with name "' . $campaigns[$i]['name'] . '" and id "' .
    $campaigns[$i]['id'] . '" was created.' . "\n";
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
