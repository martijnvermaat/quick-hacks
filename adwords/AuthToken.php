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
 * A helper class that is responsible for fetching authentication token to
 * access Google account.
 */


class AuthToken {
  var $email;
  var $passwd;
  var $account_type;
  var $service;
  var $source;
  var $res;

  function AuthToken($email, $passwd, $account_type, $service) {
    $this->email = urlencode($email);
    $this->passwd = urlencode($passwd);
    $this->account_type = $account_type;
    $this->service = $service;
    $this->source = 'Google-AWAPI PhpSamples-v4.0.0';

    $this->__login();
  }

  function __login() {
    $post_url = 'https://www.google.com/accounts/ClientLogin';
    $post_vars = 'accountType=' . $this->account_type . '&Email=' .
      $this->email . '&Passwd=' . $this->passwd . '&service=' .
      $this->service . '&source=' . $this->source;
    $ch = curl_init($post_url);
    curl_setopt($ch, CURLOPT_POST, 1);
    curl_setopt($ch, CURLOPT_POSTFIELDS, $post_vars);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, 1);
    curl_setopt($ch, CURLOPT_HEADER, 0);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, 1);
    $this->res = curl_exec($ch);
    curl_close($ch);
  }

  function __get_token($line) {
    $lines = split("\n", $this->res);
    $parts = split("=", $lines[$line]);
    return $parts[1];
  }

  function get_sid_token() {
    return $this->__get_token(0);
  }

  function get_lsid_token() {
    return $this->__get_token(1);
  }

  function get_auth_token() {
    return $this->__get_token(2);
  }
}
