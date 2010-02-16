<?php get_header(); ?>

<div id="content-wrap">
  <div id="content">
    <div class="gap">
      <?php if (have_posts()) : ?>
      <?php $post = $posts[0]; // Hack. Set $post so that the_date() works. ?>
      <?php /* If this is a category archive */ if (is_category()) { ?>
      <h2 class="pagetitle">Archive for the &#8216;<?php echo single_cat_title(); ?>&#8217;</h2>
      <?php /* If this is a daily archive */ } elseif (is_day()) { ?>
      <h2 class="pagetitle">Archive for
        <?php the_time('F jS, Y'); ?>
      </h2>
      <?php /* If this is a monthly archive */ } elseif (is_month()) { ?>
      <h2 class="pagetitle">Archive for
        <?php the_time('F, Y'); ?>
      </h2>
      <?php /* If this is a yearly archive */ } elseif (is_year()) { ?>
      <h2 class="pagetitle">Archive for
        <?php the_time('Y'); ?>
      </h2>
      <?php /* If this is an author archive */ } elseif (is_author()) { ?>
      <h2 class="pagetitle">Author Archive</h2>
      <?php /* If this is a paged archive */ } elseif (isset($_GET['paged']) && !empty($_GET['paged'])) { ?>
        <h2 class="pagetitle">Blog Archives</h2>
        <?php } ?>
      <div class="navigation">
        <div class="alignleft">
          <?php next_posts_link('&larr; Previous Entries') ?>
        </div>
        <div class="alignright">
          <?php previous_posts_link('Next Entries &rarr;') ?>
        </div>
      </div>
      <br class="clear" />
      <?php while (have_posts()) : the_post(); ?>
      <div class="post" id="post-<?php the_ID(); ?>">
        <h2 class="post-title"><a class="intitle" href="<?php the_permalink() ?>" rel="bookmark" title="Permanent Link to <?php the_title(); ?>">
          <?php the_title(); ?>
          </a> <span class="commr">
          <?php comments_popup_link('0', '1', '%'); ?>
          </span></h2>
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
          <?php the_tags('Tags: ','','<br />');?>
          <span class="catr">Category
          <?php the_category(', ') ?>
          </span> </p>
      </div>
      <?php endwhile; ?>
      <div class="navigation">
        <div class="alignleft">
          <?php next_posts_link('&laquo; Previous Entries') ?>
        </div>
        <div class="alignright">
          <?php previous_posts_link('Next Entries &raquo;') ?>
        </div>
      </div>
      <?php else : ?>
      <h2 class="center">Not Found</h2>
      <?php include (TEMPLATEPATH . '/searchform.php'); ?>
      <?php endif; ?>
</div> <!-- /gap -->
</div> <!-- /content -->
</div> <!-- /content-wrap -->
<?php get_sidebar(); ?>
<?php get_footer(); ?>
