<?php // Do not delete these lines
	if (!empty($_SERVER['SCRIPT_FILENAME']) && 'comments.php' == basename($_SERVER['SCRIPT_FILENAME']))
		die ('Open deze pagina niet direct, dank u!');

	if ( post_password_required() ) { ?>
		<p class="nocomments">Dit bericht is met een wachtwoord beveiligd. Geef het wachtwoord om reacties te kunnen zien.</p>
	<?php
		return;
}
?>
<!-- You can start editing here. -->

<?php if ( have_comments() ) : ?>
<?php if ( ! empty($comments_by_type['pings']) ) : ?>
<h3 id="pings"><?php echo fb_comment_type_count('pings'); ?>  <?php _e('Trackbacks/Pingbacks' );?> <?php if ('open' == $post->ping_status) {
							// Both Comments and Pings are open ?>
							<a href="<?php trackback_url(); ?>" rel="trackback"><img class="iright" src="<?php bloginfo('template_url'); ?>/images/ico/link.png" border="0" /></a><?php }?></h3>

<ol class="trackbacklist">
<?php wp_list_comments('type=pings&callback=list_pings'); ?>
</ol>
<?php endif; ?>



<?php if ( ! empty($comments_by_type['comment']) ) : ?>
	<h3 id="comments"><?php echo fb_comment_type_count('comment'); ?> op &#8220;<?php the_title(); ?>&#8221;</h3>

	<ol class="commentlist">
	<?php wp_list_comments('type=comment&callback=list_comment'); ?>
	</ol>

	<div class="navigation">
		<div class="alignleft"><?php previous_comments_link() ?></div>
		<div class="alignright"><?php next_comments_link() ?></div>
	</div>
<br class="clear" />
<?php endif; ?>

<br class="clear" />
 <?php else : // this is displayed if there are no comments so far ?>

	<?php if ('open' == $post->comment_status) : ?>
		<!-- If comments are open, but there are no comments. -->

	 <?php else : // comments are closed ?>
		<!-- If comments are closed. -->
		<p class="nocomments">Reageren is gesloten.</p>

	<?php endif; ?>
<?php endif; ?>


<?php if ('open' == $post->comment_status) : ?>

<div id="respond" class="comform formin">

<h3><?php comment_form_title( 'Laat een reactie achter', 'Laat een reactie achter op %s' ); ?></h3>

<div class="cancel-comment-reply">
	<small><?php cancel_comment_reply_link(); ?></small>
</div>

<?php if ( get_option('comment_registration') && !$user_ID ) : ?>
<p>Je moet <a href="<?php echo get_option('siteurl'); ?>/wp-login.php?redirect_to=<?php echo urlencode(get_permalink()); ?>">ingelogd zijn</a> om een reactie achter te kunnen laten.</p>
<?php else : ?>

<form action="<?php echo get_option('siteurl'); ?>/wp-comments-post.php" method="post" id="commentform">

<?php if ( $user_ID ) : ?>

<p>Ingelogd als <a href="<?php echo get_option('siteurl'); ?>/wp-admin/profile.php"><?php echo $user_identity; ?></a>. <a href="<?php echo wp_logout_url(get_permalink()); ?>" title="Uitloggen">Uitloggen &raquo;</a></p>

<?php else : ?>

<p><input type="text" name="author" id="author" value="<?php echo $comment_author; ?>" size="22" tabindex="1" <?php if ($req) echo "aria-required='true'"; ?> />
<label for="author"><small>Naam <?php if ($req) echo "(verplicht)"; ?></small></label></p>

<p><input type="text" name="email" id="email" value="<?php echo $comment_author_email; ?>" size="22" tabindex="2" <?php if ($req) echo "aria-required='true'"; ?> />
<label for="email"><small>Mail (wordt niet gepubliceerd) <?php if ($req) echo "(verplicht)"; ?></small></label></p>

<p><input type="text" name="url" id="url" value="<?php echo $comment_author_url; ?>" size="22" tabindex="3" />
<label for="url"><small>Website</small></label></p>

<?php endif; ?>

<!--<p><small><strong>XHTML:</strong> You can use these tags: <code><?php echo allowed_tags(); ?></code></small></p>-->
<?php if ( function_exists('smilies_clickable')) { ?>
<p><strong>Smileys</strong>:<br />
<?php smilies_clickable() ?>
</p>
<?php } ?>

<p><textarea name="comment" id="comment" cols="100%" rows="10" tabindex="4"></textarea></p>

<p><input name="submit" type="submit" id="submit" tabindex="5" value="Reactie plaatsen" />
<?php comment_id_fields(); ?>
</p>
<?php do_action('comment_form', $post->ID); ?>

</form>

<?php endif; // If registration required and not logged in ?>
</div>

<?php endif; // if you delete this the sky will fall on your head ?>
