<?php


exit();


include('config.php');
include('db.php');


$a6 = new DBConnection($db_a6);
$wp = new DBConnection($db_wp);


$a6_query = 'SELECT * FROM a6Items';
$a6_result = $a6->query($a6_query);

echo 'Converting '.$a6->num_rows($a6_result)." posts.\n\n";

while ($a6_row = $a6->f_array($a6_result)) {

    echo 'Converting: '.$a6_row['Titel'].' ... ';

    $a6_row['Titel'] = mysql_real_escape_string($a6_row['Titel']);
    $a6_row['Inhoud'] = mysql_real_escape_string($a6_row['Inhoud']);

    $nice_title = preg_replace('/[^a-z0-9]/', '', strtolower($a6_row['Titel']));
    $post = preg_replace('/\[b\](.*?)\[\/b\]/s', '<strong>$1</strong>', $a6_row['Inhoud']);
    $post = preg_replace('/\[i\](.*?)\[\/i\]/s', '<em>$1</em>', $post);
    $post = preg_replace('/\[quote\](.*?)\[\/quote\]/s', '<blockquote>$1</blockquote>', $post);

    $wp_query = 'INSERT INTO wp_posts (';
    $wp_query .= 'ID, post_author, post_date, post_date_gmt, post_content, post_title, ';
    $wp_query .= 'post_category, post_status, comment_status, ping_status, ';
    $wp_query .= 'post_name, post_modified, post_modified_gmt, post_parent, guid, ';
    $wp_query .= 'menu_order';
    $wp_query .= ') VALUES (';
    $wp_query .= $a6_row['Item_id'].", ".$a6_row['Persoon_id'].", '";
    $wp_query .= $a6_row['Tijd']."', '".$a6_row['Tijd']."', '";
    $wp_query .= $post."', '".$a6_row['Titel']."', 0, 'publish', 'open', 'open', '";
    $wp_query .= $nice_title."', '".$a6_row['Tijd']."', '".$a6_row['Tijd'];
    $wp_query .= "', 0, '/?p=".$a6_row['Item_id']."', 0)";

    $wp->query($wp_query);

    $wp_query = 'INSERT INTO wp_post2cat (rel_id, post_id, category_id) VALUES (';
    $wp_query .= $a6_row['Item_id'].', '.$a6_row['Item_id'].', 1)';

    $wp->query($wp_query);

    echo "[done]\n";

}


if ($db_error = $wp->error()) {
    print_r($db_error);
}


?>
