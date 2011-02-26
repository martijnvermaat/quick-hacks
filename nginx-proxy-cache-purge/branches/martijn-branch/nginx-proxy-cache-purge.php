<?php
/*
Plugin Name: Nginx Proxy Cache Purge
Plugin URI: http://johnlevandowski.com/
Description: Purges the nginx proxy cache when you publish or update a post or page.
Version: 0.9.4
Author: John Levandowski
Author URI: http://johnlevandowski.com/
*/

function make_purge_path($path) {
    if ($path) {
        $parts = explode('/', $path);
        if (count($parts) > 2) {
            return '/log/purge/'.implode('/', array_slice($parts, 2));
        }
    }
    return '/log/purge/';
}

function wpselect_cache($post_id) {
#post/page purge url
$link = get_permalink($post_id);
$parse = parse_url($link);
$post_url = $parse[scheme].'://'.$parse[host].make_purge_path($parse[path]);

#home page purge url
$home_page = home_url();
$parse_home = parse_url($home_page);
$home_page_url = $parse[scheme].'://'.$parse[host].make_purge_path('');

#posts page purge url
if ( get_option('show_on_front') == 'page' ) {
$posts_page = get_option('page_for_posts');
$posts_page_link = get_permalink($posts_page);
$parse_posts = parse_url($posts_page_link);
$posts_url = $parse_posts[scheme].'://'.$parse_posts[host].make_purge_path($parse_posts[path]);
} ;

#feed purge url
$feed_url = $home_page_url.'feed/';

#comments feed purge url
$comments_feed_url = $home_page_url.'comments/feed/';

#array of purge urls
$urls = array(
	$post_url, 
	$home_page_url,
	$feed_url,
	$comments_feed_url,
	$posts_url
);

#remove duplicate purge urls
$urls_unique = array_unique($urls);
foreach ($urls_unique as $uri) {
	wp_remote_get($uri);
};
}

// http://wordpress.org/support/topic/plugin-nginx-proxy-cache-purge-not-working-on-wp-292
add_action('publish_post', 'wpselect_cache');

function wpselect_footer() {
	$content = '<!-- Page created in ';
	$content .= timer_stop($display = 0, $precision = 2);
	$content .= ' seconds from ';
	$content .= get_num_queries();
	$content .= ' queries on ';
	$content .= date('m.d.y \@ H:i:s T');
	$content .= ' -->';
	echo $content;
}

add_action('wp_footer', 'wpselect_footer');
?>
