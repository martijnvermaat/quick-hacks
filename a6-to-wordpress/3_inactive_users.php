<?php


exit();


include('config.php');
include('db.php');


$a6 = new DBConnection($db_a6);
$wp = new DBConnection($db_wp);


$wp_query = 'SELECT * FROM wp_users';
$wp_result = $wp->query($wp_query);

echo "Removing inactive users...\n\n";

while ($wp_row = $wp->f_array($wp_result)) {

    if (($wp_row['user_login'] != 'Annemiek Bax') && ($wp_row['user_login'] != 'Loes')) {

        $p_query = 'SELECT COUNT(*) FROM wp_posts WHERE post_author = '.$wp_row['ID'].' GROUP BY post_author';
        $p_result = $wp->query($p_query);

        if ($wp->result($p_result) < 1) {

            echo 'Removing user '.$wp_row['user_login'].' ... ';

            $wp_query = 'DELETE FROM wp_users WHERE ID = '.$wp_row['ID'];
            $wp->query($wp_query);

            echo "[done]\n";

        }

    } else {

        echo 'Skipping user '.$wp_row['user_login']."\n";

    }

}


if ($db_error = $wp->error()) {
    print_r($db_error);
}


?>
