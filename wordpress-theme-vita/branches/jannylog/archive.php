<?php get_header(); ?>

<div id="content-wrap">
  <div id="content">
    <div class="gap">
      <?php if (have_posts()) : ?>
      <?php $post = $posts[0]; // Hack. Set $post so that the_date() works. ?>
      <?php /* If this is a category archive */ if (is_category()) { ?>
      <h2 class="pagetitle">Archief voor &#8216;<?php echo single_cat_title(); ?>&#8217;</h2>
      <?php /* If this is a daily archive */ } elseif (is_day()) { ?>
      <h2 class="pagetitle">Archief voor
        <?php the_time('F jS, Y'); ?>
      </h2>
      <?php /* If this is a monthly archive */ } elseif (is_month()) { ?>
      <h2 class="pagetitle">Archief voor
        <?php the_time('F, Y'); ?>
      </h2>
      <?php /* If this is a yearly archive */ } elseif (is_year()) { ?>
      <h2 class="pagetitle">Archief voor
        <?php the_time('Y'); ?>
      </h2>
      <?php /* If this is an author archive */ } elseif (is_author()) { ?>
      <h2 class="pagetitle">Schrijversarchief</h2>
      <?php /* If this is a paged archive */ } elseif (isset($_GET['paged']) && !empty($_GET['paged'])) { ?>
        <h2 class="pagetitle">Weblogarchieven</h2>
        <?php } ?>
      <div class="navigation">
        <div class="alignleft">
          <?php next_posts_link('&larr; Vorige berichten') ?>
        </div>
        <div class="alignright">
          <?php previous_posts_link('Volgende berichten &rarr;') ?>
        </div>
      </div>
      <br class="clear" />
      <?php while (have_posts()) : the_post(); ?>
      <div class="post" id="post-<?php the_ID(); ?>">
        <h2 class="post-title"><a class="intitle" href="<?php the_permalink() ?>" rel="bookmark" title="Permanente link naar <?php the_title(); ?>">
          <?php the_title(); ?>
          </a> <span class="commr">
          <?php comments_popup_link('0', '1', '%'); ?>
          </span></h2>
        <div class="timr"> Geplaatst op
          <?php the_time('F d, Y') ?>
          door
          <?php the_author() ?>
          <?php edit_post_link('e', '<span class="editr">[', '] </span>'); ?>
        </div>
        <div class="entry">
          <?php the_content('Lees de rest van dit bericht &rarr;'); ?>
        </div>
        <p class="postmetadata">
          <?php the_tags('Onderwerpen: ',', ','<br />');?>
<!--          <span class="catr">Categorie
          <?php the_category(', ') ?>
          </span> -->
        </p>
      </div>
      <?php endwhile; ?>
      <div class="navigation">
        <div class="alignleft">
          <?php next_posts_link('&laquo; Vorige berichten') ?>
        </div>
        <div class="alignright">
          <?php previous_posts_link('Volgende berichten &raquo;') ?>
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
