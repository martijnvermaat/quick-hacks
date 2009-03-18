<?php
// check functions
  if ( function_exists('wp_list_bookmarks') ) //used to check WP 2.1 or not
    $numposts = $wpdb->get_var("SELECT COUNT(*) FROM $wpdb->posts WHERE post_type='post' and post_status = 'publish'");
	else
    $numposts = $wpdb->get_var("SELECT COUNT(*) FROM $wpdb->posts WHERE post_status = 'publish'");
  if (0 < $numposts) $numposts = number_format($numposts); 
	$numcmnts = $wpdb->get_var("SELECT COUNT(*) FROM $wpdb->comments WHERE comment_approved = '1'");
		if (0 < $numcmnts) $numcmnts = number_format($numcmnts);
// ----------------

function J_ShowAbout() { ?>

<li class="about boxr">
  <h2>Over mij</h2>
  <p>Aenean dui quam, pellentesque ut, commodo ac, tempor aliquam, turpis. Etiam accumsan rhoncus nisi. Morbi velit enim, mollis et, elementum sit amet, egestas sed, diam. Curabitur scelerisque, nulla et facilisis fringilla, sapien elit auctor augue, at porttitor ipsum nibh faucibus ligula.</p>
  <p class="stats">Ik heb: <span class="catr"><a title="<?php global $numcmnts;echo $numcmnts;?> berichten">
    <?php global $numposts;echo $numposts; ?>
    </a> berichten</span>, <span class="comr"><a title="<?php global $numcmnts;echo $numcmnts;?> reacties">
    <?php global $numcmnts;echo $numcmnts;?>
    </a></span> reacties</p>
</li>
<?php }	function J_ShowRecentPosts() {?>
<li class="boxr lasties">
  <h3>
    <?php _e('Recent Posts'); ?>
  </h3>
  <ul>
    <?php $my_query = new WP_Query('showposts=10');
  while ($my_query->have_posts()) : $my_query->the_post();
  $do_not_duplicate = $post->ID; ?>
    <!-- Do stuff... -->
    <li><span>
      <?php the_time('m - d') ?>
      </span>
      <div class="inin"><a href="<?php the_permalink() ?>" rel="bookmark" title="Permanente link naar <?php the_title(); ?>">
        <?php the_title(); ?>
        </a></div>
    </li>
    <?php endwhile; ?>
  </ul>
</li>
<?php }	?>
<?php

if ( function_exists('register_sidebars') )
	register_sidebars(2);

$jh_trackbacks = array();
$jh_comments = array();

function split_comments( $source ) {

    if ( $source ) foreach ( $source as $comment ) {

        global $jh_trackbacks;
        global $jh_comments;

        if ( $comment->comment_type == 'trackback' || $comment->comment_type == 'pingback' ) {
            $jh_trackbacks[] = $comment;
        } else {
            $jh_comments[] = $comment;
        }
    }
}

define('HEADER_IMAGE', '%s/images/splash/tofu.jpg'); // %s is theme dir uri
define('HEADER_IMAGE_WIDTH', 970);
define('HEADER_IMAGE_HEIGHT', 150);
define('HEADER_TEXTCOLOR', 'FFFFFF');
//define('HEADER_H1', '%s/images/ico/h1-bg.png');

function admin_header_style() { ?>
<style type="text/css">
#splash,#headimg {
        background: #E0303A url(<?php header_image(); ?>) right top no-repeat;
        height: <?php echo HEADER_IMAGE_HEIGHT; ?>px;
        width: <?php echo HEADER_IMAGE_WIDTH; ?>px;
        position: relative;
}


#headimg h1 a {
	font-size: 120%;
	padding: 6px 15px 10px;
	letter-spacing: -2pt;
	background: transparent url(<?php bloginfo('template_url'); ?>/images/ico/h1-bg.png);
	color: #fff;
	text-decoration: none;
	position: absolute;
	top: 0;
	left: 20px;
}
#headimg #desc {
	display: none;
}

</style>
<?php }

function header_style() { ?>
<style type="text/css">
#splash {
	background: #BDE701 url(<?php header_image(); ?>) 0 0 no-repeat;
    height: 150px;
}

<?php if ( 'blank' == get_header_textcolor() ) { ?>

#splash h1 {
        display: none;
}

<?php }else{ ?>

#splash h1 a{
        color: #<?php header_textcolor(); ?>;
}
#splash .description {
        display: none;
}
<?php } ?>

</style>
<?php }

if ( function_exists('add_custom_image_header') ) {
  add_custom_image_header('header_style', 'admin_header_style');
} 

/* There you go, have a nice day */
/* WordPress 2.7 and Later on */
add_filter('comments_template', 'legacy_comments');
function legacy_comments($file) {
	if(!function_exists('wp_list_comments')) 	$file = TEMPLATEPATH . '/old.comments.php';
	return $file;
}

function list_pings($comment, $args, $depth) {
       $GLOBALS['comment'] = $comment;
?>
        <li id="comment-<?php comment_ID(); ?>">
        <span class="timer">
        <?php comment_date('d m y'); ?> <?php comment_time('H:i') ?></span>

        <h4><?php comment_author_link(); ?></h4>
        </li>
<?php } 

function list_comment($comment, $args, $depth) {
   $GLOBALS['comment'] = $comment; ?>
   <li <?php comment_class(); ?> id="comment-<?php comment_ID() ?>">
   <div id="div-comment-<?php comment_ID() ?>" class="thechild">
      <div class="leftarea">
         <?php echo get_avatar($comment, 52); ?>
	  </div>
      <div class="rightarea">      
      <div class="comment-author vcard by">
         <?php printf(__('<cite class="fn">%s</cite> <span class="says">zegt:</span>'), get_comment_author_link()) ?>
      </div>
      <?php if ($comment->comment_approved == '0') : ?>
         <em><?php _e('Your comment is awaiting moderation.') ?></em>
         <br />
      <?php endif; ?>

      <div class="comment-meta commentmetadata"><a href="<?php echo htmlspecialchars( get_comment_link( $comment->comment_ID ) ) ?>"><?php printf(__('%1$s at %2$s'), get_comment_date(),  get_comment_time()) ?></a><?php edit_comment_link(__('(Edit)'),'  ','') ?></div>
	 <div class="c-entry">
      <?php comment_text() ?>
</div>
      <div class="reply">
         <?php comment_reply_link(array_merge( $args, array('add_below' => 'div-comment', 'depth' => $depth, 'max_depth' => $args['max_depth']))) ?>
      </div>
    </div>
      </div>
   </li>               
<?php
        }
/**
 * count for Trackback, pingback, comment, pings
 *
 * use it:
 * fb_comment_type_count('ping');
 * fb_comment_type_count('comment');
 */
if ( !function_exists('fb_comment_type_count') ) {
	function fb_get_comment_type_count($type='all', $post_id = 0) {
		global $cjd_comment_count_cache, $id, $post;
 
		if ( !$post_id )
			$post_id = $post->ID;
		if ( !$post_id )
			return;
 
		if ( !isset($cjd_comment_count_cache[$post_id]) ) {
			$p = get_post($post_id);
			$p = array($p);
			update_comment_type_cache($p);
		}
 
		if ( $type == 'pingback' || $type == 'trackback' || $type == 'comment' )
			return $cjd_comment_count_cache[$post_id][$type];
		elseif ( $type == 'pings' )
			return $cjd_comment_count_cache[$post_id]['pingback'] + $cjd_comment_count_cache[$post_id]['trackback'];
		else
			return array_sum((array) $cjd_comment_count_cache[$post_id]);
	}
 
	// comment, trackback, pingback, pings
	function fb_comment_type_count($type = 'all', $post_id = 0) {
		echo fb_get_comment_type_count($type, $post_id);
	}
}

 function update_comment_type_cache(&$queried_posts) {
global $cjd_comment_count_cache, $wpdb;

if ( !$queried_posts )
return $queried_posts;

foreach ( (array) $queried_posts as $post )
if ( !isset($cjd_comment_count_cache[$post->ID]) )
$post_id_list[] = $post->ID;

if ( $post_id_list ) {
$post_id_list = implode(',', $post_id_list);

foreach ( array('','pingback', 'trackback') as $type ) {
$counts = $wpdb->get_results("SELECT ID, COUNT( comment_ID ) AS ccount
FROM $wpdb->posts
LEFT JOIN $wpdb->comments ON ( comment_post_ID = ID AND comment_approved = '1' AND comment_type='$type' )
WHERE post_status = 'publish' AND ID IN ($post_id_list)
GROUP BY ID");

if ( $counts ) {
if ( '' == $type )
$type = 'comment';
foreach ( $counts as $count )
$cjd_comment_count_cache[$count->ID][$type] = $count->ccount;
}
}
}
return $queried_posts;
}
?>
