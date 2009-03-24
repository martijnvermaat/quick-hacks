<?php get_header(); ?>

<div id="content" class="widecolumn">
  <?php if (have_posts()) : while (have_posts()) : the_post(); ?>
  <div class="navigation">
    <div class="alignleft">&nbsp;</div>
    <div class="alignright">&nbsp;</div>
  </div>
  <?php $attachment_link = get_the_attachment_link($post->ID, true, array(450, 800)); // This also populates the iconsize for the next line ?>
  <?php $_post = &get_post($post->ID); $classname = ($_post->iconsize[0] <= 128 ? 'small' : '') . 'attachment'; // This lets us style narrow icons specially ?>
  <div class="post" id="post-<?php the_ID(); ?>">
    <h2><a href="<?php echo get_permalink($post->post_parent); ?>" rev="attachment"><?php echo get_the_title($post->post_parent); ?></a> &raquo; <a href="<?php echo get_permalink() ?>" rel="bookmark" title="Permanente link: <?php the_title(); ?>">
      <?php the_title(); ?>
      </a></h2>
    <div class="entry">
      <p class="<?php echo $classname; ?>"><?php echo $attachment_link; ?><br />
        <?php echo basename($post->guid); ?></p>
      <?php the_content('<p class="serif">Lees de rest van dit bericht &raquo;</p>'); ?>
      <?php wp_link_pages(array('before' => '<p><strong>Pagina\'s:</strong> ', 'after' => '</p>', 'next_or_number' => 'number')); ?>
      <p class="postmetadata alt"> <small> Dit bericht is geplaast
        <?php /* This is commented, because it requires a little adjusting sometimes.
							You'll need to download this plugin, and follow the instructions:
							http://binarybonsai.com/archives/2004/08/17/time-since-plugin/ */
							/* $entry_datetime = abs(strtotime($post->post_date) - (60*120)); echo time_since($entry_datetime); echo ' ago'; */ ?>
        op
        <?php the_time('l, d F, Y') ?>
        om
        <?php the_time() ?>
<!--        and is filed under
        <?php the_category(', ') ?> -->
        .
        Je kunt reacties op dit bericht volgen via de
        <?php comments_rss_link('RSS 2.0'); ?>
        feed.
        <?php if (('open' == $post-> comment_status) && ('open' == $post->ping_status)) {
							// Both Comments and Pings are open ?>
        Je kunt <a href="#respond">een reactie achterlaten</a>, of <a href="<?php trackback_url(true); ?>" rel="trackback">een trackback doen</a> vanaf je eigen site.
        <?php } elseif (!('open' == $post-> comment_status) && ('open' == $post->ping_status)) {
							// Only Pings are Open ?>
        Reageren is op dit moment gesloten, maar je kunt <a href="<?php trackback_url(true); ?> " rel="trackback">een trackback doen</a> vanaf je eigen site.
        <?php } elseif (('open' == $post-> comment_status) && !('open' == $post->ping_status)) {
							// Comments are open, Pings are not ?>
        Je kunt onderaan een reactie achterlaten. Trackbacks zijn op dit moment niet toegestaan.
        <?php } elseif (!('open' == $post-> comment_status) && !('open' == $post->ping_status)) {
							// Neither Comments, nor Pings are open ?>
        Reacties en trackbacks zijn op dit moment niet toegestaan.
        <?php } edit_post_link('Bewerk dit bericht.','',''); ?>
        </small> </p>
    </div>
  </div>
  <?php comments_template(); ?>
  <?php endwhile; else: ?>
  <p>Sorry, geen attachments voldoen aan je criteria.</p>
  <?php endif; ?>
</div>
<?php get_sidebar(); ?>
<?php get_footer(); ?>
