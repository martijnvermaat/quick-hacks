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
 * A helper class for instantiating NuSOAP, regardless of the PHP version in
 * use. In PHP5, a php_soap extension was introduced with a new class named
 * 'soapclient'. As a result, the NuSOAP library renamed its class to
 * 'nusoap_client'.
 */

require_once('../nusoap/nusoap.php');


class SoapClientFactory{
  function GetClient(
      $endpoint, $wsdl = false, $proxyhost = false, $proxyport = false,
      $proxyusername = false, $proxypassword = false, $timeout = 0,
      $response_timeout = 30) {
    if (!extension_loaded('soap')) {
      return new soapclient($endpoint, $wsdl, $proxyhost, $proxyport,
        $proxyusername, $proxypassword, $timeout, $response_timeout);
    } else {
      return new nusoap_client($endpoint, $wsdl, $proxyhost, $proxyport,
        $proxyusername, $proxypassword, $timeout, $response_timeout);
    }
  }
}
