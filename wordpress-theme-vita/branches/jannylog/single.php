<?php get_header(); ?>

<div id="content-wrap">
  <div id="content">
    <div class="gap">
      <?php if (have_posts()) : while (have_posts()) : the_post(); ?>
      <div class="post" id="post-<?php the_ID(); ?>">
        <h2 class="post-title"><a class="intitle" href="<?php the_permalink() ?>" rel="bookmark" title="Permanent Link to <?php the_title(); ?>">
          <?php the_title(); ?>
          </a></h2>
        <div class="timr"> Posted on
          <?php the_time('F d, Y') ?>
          by
          <?php the_author() ?>
          <?php edit_post_link('e', '<span class="editr">[', '] </span>'); ?>
        </div>
        <div class="entry">
          <?php the_content('Read the rest of this entry &rarr;'); ?>
        </div>
        <p class="postmetadata">
          <?php the_tags('Tags: ',', ','<br />');?>
          <span class="catr">Category
          <?php the_category(', ') ?>
          </span>
			<?php if (('open' == $post-> comment_status) && ('open' == $post->ping_status)) {
				// Both Comments and Pings are open ?>
				<br />Trackback: <a href="<?php trackback_url(); ?>" rel="trackback">trackback</a> from your own site.

			<?php } elseif (!('open' == $post-> comment_status) && ('open' == $post->ping_status)) {
				// Only Pings are Open ?>
				<br />Responses are currently closed, but you can <a href="<?php trackback_url(); ?> " rel="trackback">trackback</a> from your own site.

			<?php } elseif (('open' == $post-> comment_status) && !('open' == $post->ping_status)) {
				// Comments are open, Pings are not ?>
				<br />You can skip to the end and leave a response. Pinging is currently not allowed.

			<?php } elseif (!('open' == $post-> comment_status) && !('open' == $post->ping_status)) {
				// Neither Comments, nor Pings are open ?>
				<br />Both comments and pings are currently closed.

			<?php } ?>


          </p>
      </div>
	<?php comments_template('', true); ?>

      <?php endwhile; else: ?>
      <p>Sorry, no posts matched your criteria.</p>
      <?php endif; ?>
      <div class="navigation">
        <div class="alignleft">
          <?php previous_post_link('&larr; %link') ?>
        </div>
        <div class="alignright">
          <?php next_post_link('%link &rarr;') ?>
        </div>
      </div>
      <br class="clear" />
</div> <!-- /gap -->
</div> <!-- /content -->
</div> <!-- /content-wrap -->
<?php get_sidebar(); ?>
<?php get_footer(); ?>
