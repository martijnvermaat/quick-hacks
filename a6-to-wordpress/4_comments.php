<?php


exit();


include('config.php');
include('db.php');


$a6 = new DBConnection($db_a6);
$wp = new DBConnection($db_wp);


$a6_query = 'SELECT * FROM a6Reacties';
$a6_result = $a6->query($a6_query);

echo 'Converting '.$a6->num_rows($a6_result)." comments.\n\n";

while ($a6_row = $a6->f_array($a6_result)) {

    echo 'Converting: '.$a6_row['Tijd'].' ... ';

    $a6_row['Inhoud'] = mysql_real_escape_string($a6_row['Inhoud']);

    $post = preg_replace('/\[b\](.*?)\[\/b\]/s', '<strong>$1</strong>', $a6_row['Inhoud']);
    $post = preg_replace('/\[i\](.*?)\[\/i\]/s', '<em>$1</em>', $post);
    $post = preg_replace('/\[quote\](.*?)\[\/quote\]/s', '<blockquote>$1</blockquote>', $post);
    $post = preg_replace('/\[quote=[^\]]*\](.*?)\[\/quote\]/s', '<blockquote>$1</blockquote>', $post);

    if ($a6_row['Persoon_id'] == 1) {
        $author = 'Martijn';
    } else {
        $p_query = 'SELECT Naam FROM a6Personen WHERE Persoon_id = '.$a6_row['Persoon_id'];
        $p_result = $a6->query($p_query);
        $author = $a6->result($p_result);
    }

    $author = mysql_real_escape_string($author);

    $wp_query = 'INSERT INTO wp_comments (';
    $wp_query .= 'comment_ID, comment_post_ID, comment_author, comment_author_IP, ';
    $wp_query .= 'comment_date, comment_date_gmt, comment_content, comment_karma, ';
    $wp_query .= 'comment_approved, comment_parent, user_id';
    $wp_query .= ') VALUES (';
    $wp_query .= $a6_row['Reactie_id'].", ".$a6_row['Item_id'].", '";
    $wp_query .= $author."', '127.0.0.1', '".$a6_row['Tijd']."', '".$a6_row['Tijd']."', '";
    $wp_query .= $post."', 0, '1', 0, 0)";

    $wp->query($wp_query);

    echo "[done]\n";

}


if ($db_error = $wp->error()) {
    print_r($db_error);
}


?>
