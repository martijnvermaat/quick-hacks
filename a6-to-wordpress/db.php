<?php


/*
	Database class
	A class implementing a database abstraction layer for your application

	Author:			Martijn Vermaat [mvermaat@cs.vu.nl]
	Version:		0.99e
	Modified:		2004-07-21, Martijn Vermaat
	Modifications:	* Support for MS SQL Server
					* Added errorsupport for SQL Server
					* Updated insert_id() support for SQL Server
					* Changed some string error identifiers
                    * Updated mysql_connect() function to use 'new_link' parameter
                    * Fixed minor bug in error reporting function
                    * Added get_results() function
	ToDo:			* Better error reporting
					* Support for more DBMs
					* Documentation :D
*/


class DBConnection {

	var $db = 0;
	var $host = 'localhost';
	var $user = 'root';
	var $password = '';
	var $database = '';
	var $server = '';
	var $pconnect = false;
	var $error = '';
	var $mysqlerror = '';
	var $errorquery = '';
	var $debug_querystring = true;


// Constructor, connects to the database

function DBConnection($vars) {

	$this->host = $vars['Host'];
	$this->user = $vars['User'];
	$this->password = $vars['Password'];
	$this->database = $vars['Database'];
	$this->server = $vars['Server'];
	$this->pconnect = $vars['PConnect'];

	if ($this->server == 'mssql') {

		// Microsoft SQL Server

		if ($this->pconnect) {
			$db = @mssql_pconnect($this->host, $this->user, $this->password);
		} else {
			$db = @mssql_connect($this->host, $this->user, $this->password);
		}

		if ($db) {
			if (!@mssql_select_db($this->database, $db)) {
				if (!$this->error) {
					$this->error = 'dbSelect';
					$this->mysqlerror = mssql_get_last_message();
				}
				return false;
			}
		} else {
			if (!$this->error) {
				$this->error = 'dbConnect';
				if ($error = mssql_get_last_message()) {
					$this->mysqlerror = mssql_get_last_message();
				} else {
					$this->mysqlerror = 'Unable to connect to MS SQL Server at '.$this->host;
				}
			}
		}

	} else {

		// MySQL

		if ($this->pconnect) {
			$db = @mysql_pconnect($this->host, $this->user, $this->password);
		} else {
            // As of 4.2.x, mysql_connect() supports an 'new_link' parameter, ensuring
            // existing connection id's will not be overwritten
            if (PHP_VERSION >= '4.2') {
    			$db = @mysql_connect($this->host, $this->user, $this->password, true);
            } else {
    			$db = @mysql_connect($this->host, $this->user, $this->password);
            }
		}

		if ($db) {
			if (!@mysql_select_db($this->database, $db)) {
				if (!$this->error) {
					$this->error = 'dbSelect';
					$this->mysqlerror = mysql_error();
				}
				return false;
			}
		} else {
			if (!$this->error) {
				$this->error = 'dbConnect';
				$this->mysqlerror = mysql_error();
			}
		}

	}

	$this->db = $db;
	return $db;

}


// Returns result pointer for query

function query($query) {

	if ($this->server == 'mssql') {

		// Microsoft SQL Server

		if (!($result = @mssql_query($query, $this->db))) {
			if (!$this->error) {
				$this->errorquery = $query;
				$this->error = 'dbQuery';
				$this->mysqlerror = mssql_get_last_message();
			}
		}

	} else {

		// MySQL

		if (!($result = @mysql_query($query, $this->db))) {
			if (!$this->error) {
				$this->errorquery = $query;
				$this->error = 'dbQuery';
				$this->mysqlerror = mysql_error();
			}
		}

	}

	return $result;

}


// Fetches an array from a resultset

function f_array($result) {

	if ($this->server == 'mssql') {

		// Microsoft SQL Server

		$a = @mssql_fetch_array($result);

	} else {

		// MySQL

		$a = @mysql_fetch_array($result);
		if ($e = mysql_error()) {
			if (!$this->error) {
				$this->error = 'dbFetchArray';
				$this->mysqlerror = $e;
			}
		}

	}

	return $a;

}


// Fetches a row from a resultset

function f_row($result) {

	if ($this->server == 'mssql') {

		// Microsoft SQL Server
		// Warning: not tested!

		$a = @mssql_fetch_row($result);

	} else {

		// MySQL

		$a = @mysql_fetch_row($result);
		if ($e = mysql_error()) {
			if (!$this->error) {
				$this->error = 'dbFetchRow';
				$this->mysqlerror = $e;
			}
		}

	}

	return $a;

}


// Returns a field from a resultset

function result($result, $field = 0) {

	if ($this->server == 'mssql') {

		// Microsoft SQL Server

		$a = @mssql_result($result, 0, $field);

	} else {

		// MySQL

		$a = @mysql_result($result, $field);
		if ($e = mysql_error()) {
			if (!$this->error) {
				$this->error = 'dbResult';
				$this->mysqlerror = $e;
			}
		}

	}

	return $a;

}


// Fetches complete resultset in an array

function get_results($result) {

    $r = array();

	if ($this->server == 'mssql') {

		// Microsoft SQL Server

        while ($row = @mssql_fetch_array($result)) {
            array_push($r, $row);
        }


	} else {

		// MySQL

        while ($row = @mysql_fetch_array($result)) {
            array_push($r, $row);
        }

        if ($e = mysql_error()) {
            if (!$this->error) {
                $this->error = 'dbGetResults';
                $this->mysqlerror = $e;
            }
        }

	}

	return $r;

}


// Returns number of rows in a resultset

function num_rows($result) {

	if ($this->server == 'mssql') {

		// Microsoft SQL Server
		// Warning: not tested!

		$n = @mssql_num_rows($result);

	} else {

		// MySQL

		$n = @mysql_num_rows($result);
		if ($e = mysql_error()) {
			if (!$this->error) {
				$this->error = 'dbNumRows';
				$this->mysqlerror = $e;
			}
		}

	}

	return $n;

}


// Returns number of affected rows in previous MySQL operation

function affected_rows() {

	if ($this->server == 'mssql') {

		// Microsoft SQL Server
		// Warning: not tested!

		$a = @mssql_affected_rows($this->db);

	} else {

		// MySQL

		$a = @mysql_affected_rows($this->db);
		if ($e = mysql_error()) {
			if (!$this->error) {
				$this->error = 'dbAffectedRows';
				$this->mysqlerror = $e;
			}
		}

	}

	return $a;

}


// Returns ID generated by last insert query

function insert_id() {

	if ($this->server == 'mssql') {

		// Microsoft SQL Server

		$result = $this->query("SELECT @@IDENTITY");
		$a = $this->result($result);

	} else {

		// MySQL

		$a = @mysql_insert_id($this->db);
		if ($e = mysql_error()) {
			if (!$this->error) {
				$this->error = 'dbInsertID';
				$this->mysqlerror = $e;
			}
		}

	}

	return $a;

}


// Returns server value

function server() {

	return $this->server;

}


// Returns class error and MySQL error

function error() {
	if ($this->error || $this->mysqlerror) {
		$system_msg = $this->mysqlerror.( ($this->debug_querystring && $this->errorquery) ? '<br /><br />'.$this->errorquery : '' );
		return array('text'=>$this->error, 'system_msg'=>$system_msg);
	} else {
		return false;
	}
}


// End of class

}


?>
