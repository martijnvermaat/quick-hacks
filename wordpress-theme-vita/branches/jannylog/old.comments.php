<?php // Do not delete these lines
	if ('comments.php' == basename($_SERVER['SCRIPT_FILENAME']))
		die ('Please do not load this page directly. Thanks!');

	if (!empty($post->post_password)) { // if there's a password
		if ($_COOKIE['wp-postpass_' . COOKIEHASH] != $post->post_password) {  // and it doesn't match the cookie
			?>

<p class="nocomments">This post is password protected. Enter the password to view comments.
<p>
  <?php
			return;
		}
	}

	/* This variable is for alternating comment background */
	$oddcomment = 'alt';
?>
  <!-- You can start editing here. -->
  <?php 
	$ix=0;
?>
  <br class="clear" />
  <!-- test -->
  <?php
global $jh_comments;
global $jh_trackbacks;

split_comments( $comments );
?>
  <?php

$ccount = count($jh_comments);
$tcount = count($jh_trackbacks);

?>
  <? // Begin Trackbacks ?>
  <?php foreach ($comments as $comment) : ?>
  <? if ($comment->comment_type == "trackback" || $comment->comment_type == "pingback" || ereg("<pingback />", $comment->comment_content) || ereg("<trackback />", $comment->comment_content)) { ?>
  <? if (!$runonce) { $runonce = true; ?>
<h3 id="trackbacks"><?php echo $tcount; ?> Trackbacks &amp; Pingbacks  <?php if ('open' == $post->ping_status) {
							// Both Comments and Pings are open ?>
							<a href="<?php trackback_url(); ?>" rel="trackback"><img class="iright" src="<?php bloginfo('template_url'); ?>/images/ico/link.png" border="0" /></a><?php }?></h3>
<ol class="trackbacklist">
  <? } ?>
  <li class="track" id="comment-<?php comment_ID() ?>"> <span class="timer"> <a href="#comment-<?php comment_ID() ?>">
    <?php comment_date() ?>
    <?php comment_time('H:i') ?>
    </a></span>
    <h4><?php comment_author_link() ?></h4>
  </li>
  <? } ?>
  <?php endforeach; ?>
  <? if ($runonce) { ?>
</ol>
<? } ?>
<? // End Trackbacks ?>
<?php if ($comments) : ?>
<h3 id="comments"><?php echo $ccount;?> Reacties</h3>
<ol class="commentlist">
  <?php foreach ($comments as $comment) : ?>
  <?php if($comment->comment_type == '') { ?>
  <li class="comment <?php echo $oddcomment; ?>" id="comment-<?php comment_ID();$ix++; ?>">
    <div class="leftarea">
      <?php 
		if (function_exists('get_avatar')) {
		echo get_avatar( get_comment_author_email(), $size = '40', $default = '' );
		} else {
		//alternate gravatar code for < 2.5
		$size = 40;
		$grav_url = "http://www.gravatar.com/avatar.php?gravatar_id=
		 " . md5($email) . "&default=" . urlencode($default) . "&size=" . $size;
		echo "<img src='$grav_url'/>";
		}
		?>
    </div>
    <div class="rightarea">
      <div class="numero"><a href="#comment-<?php comment_ID(); ?>">
        <?= $ix; ?>
        </a></div>
      <strong>
      <?php comment_author_link() ?>
      </strong>
      <?php if ($comment->comment_approved == '0') : ?>
      <em>Your comment is awaiting moderation.</em>
      <?php endif; ?>
      <?php comment_text() ?>
      <small class="commentmetadata"><a href="#comment-<?php comment_ID() ?>" title="">
      <?php comment_date('F jS, Y') ?>
      om
      <?php comment_time() ?>
      </a>
      <?php edit_comment_link('e','',''); ?>
      </small> </div>
    <br class="clear" />
  </li>
  <?php /* Changes every other comment to a different class */
		if ('alt' == $oddcomment) $oddcomment = '';
		else $oddcomment = 'alt';
	?>
  <?php } ?>
  <?php endforeach; /* end for each comment */ ?>
</ol>
<?php else : // this is displayed if there are no comments so far ?>
<?php if ('open' == $post->comment_status) : ?>
<!-- If comments are open, but there are no comments. -->
<?php else : // comments are closed ?>
<!-- If comments are closed. -->
<p class="nocomments">Comments are closed.</p>
<?php endif; ?>
<?php endif; ?>
<?php if ('open' == $post->comment_status) : ?>
<div class="formin">
  <h3 id="respond">Leave a Reply</h3>
  <?php if ( get_option('comment_registration') && !$user_ID ) : ?>
  <p>You must be <a href="<?php echo get_option('siteurl'); ?>/wp-login.php?redirect_to=<?php the_permalink(); ?>">logged in</a> to post a comment.</p>
  <?php else : ?>
  <form action="<?php echo get_option('siteurl'); ?>/wp-comments-post.php" method="post" id="commentform">
    <?php if ( $user_ID ) : ?>
    <p>Logged in as <a href="<?php echo get_option('siteurl'); ?>/wp-admin/profile.php"><?php echo $user_identity; ?></a>. <a href="<?php echo get_option('siteurl'); ?>/wp-login.php?action=logout" title="Log out of this account">Logout &raquo;</a></p>
    <?php else : ?>
    <p>
      <input type="text" name="author" id="author" value="<?php echo $comment_author; ?>" size="22" tabindex="1" />
      <label for="author"><small>Name
      <?php if ($req) echo "(required)"; ?>
      </small></label>
    </p>
    <p>
      <input type="text" name="email" id="email" value="<?php echo $comment_author_email; ?>" size="22" tabindex="2" />
      <label for="email"><small>Mail (will not be published)
      <?php if ($req) echo "(required)"; ?>
      </small></label>
    </p>
    <p>
      <input type="text" name="url" id="url" value="<?php echo $comment_author_url; ?>" size="22" tabindex="3" />
      <label for="url"><small>Website</small></label>
    </p>
    <?php endif; ?>
    <!--<p><small><strong>XHTML:</strong> You can use these tags: <?php echo allowed_tags(); ?></small></p>-->
    <p>
      <textarea name="comment" id="comment" cols="100%" rows="10" tabindex="4"></textarea>
    </p>
    <p>
      <input name="submit" type="submit" id="submit" tabindex="5" value="Submit Comment" />
      <input type="hidden" name="comment_post_ID" value="<?php echo $id; ?>" />
    </p>
    <?php do_action('comment_form', $post->ID); ?>
  </form>
  <?php endif; // If registration required and not logged in ?>
</div>
<?php endif; // if you delete this the sky will fall on your head ?>
