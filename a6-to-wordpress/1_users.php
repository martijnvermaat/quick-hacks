<?php


exit();


include('config.php');
include('db.php');


$a6 = new DBConnection($db_a6);
$wp = new DBConnection($db_wp);


$a6_query = 'SELECT * FROM a6Personen';
$a6_result = $a6->query($a6_query);

echo 'Converting '.$a6->num_rows($a6_result)." users.\n\n";

while ($a6_row = $a6->f_array($a6_result)) {

    echo 'Converting: '.$a6_row['Naam'].' ... ';

    $a6_row['Naam'] = mysql_real_escape_string($a6_row['Naam']);
    $a6_row['Homepage'] = mysql_real_escape_string($a6_row['Homepage']);
    $a6_row['Email'] = mysql_real_escape_string($a6_row['Email']);

    $nice_name = preg_replace('/[^a-z0-9]/', '', strtolower($a6_row['Naam']));

    $wp_query = 'INSERT INTO wp_users (';
    $wp_query .= 'ID, user_login, user_firstname, user_nickname, ';
    $wp_query .= 'user_nicename, user_email, user_url, ';
    $wp_query .= 'user_registered, user_level, user_idmode, user_status';
    $wp_query .= ') VALUES (';
    $wp_query .= $a6_row['Persoon_id'].", '".$a6_row['Naam']."', '";
    $wp_query .= $a6_row['Naam']."', '".$a6_row['Naam']."', '";
    $wp_query .= $nice_name."', '".$a6_row['Email']."', '".$a6_row['Homepage'];
    $wp_query .= "', '".$a6_row['Tijd']."', 1, 'nickname', 0)";


    $wp->query($wp_query);
    echo "[done]\n";

}


if ($db_error = $wp->error()) {
    print_r($db_error);
}


?>
