<?php
$this->includeTemplate($GLOBALS['top_include']);
?>

<p>
<?php echo T_('These pages are based on <a href="http://sourceforge.net/projects/scuttle/">Scuttle</a>, an open-source project licensed under the <a href="http://www.gnu.org/copyleft/gpl.html"><acronym title="GNU\'s Not Unix">GNU</acronym> General Public License</a>. This means you can host it on your own web server for free, whether it is on the Internet, a private network or just your own computer.'); ?></li>
</p>

<p>
<?php echo T_('The changes I made to Scuttle (only a few) can be found in my <a href="http://svn.vermaat.name/hacks/scuttle/">Subversion repository</a>.'); ?>
</p>

<?php
$this->includeTemplate($GLOBALS['bottom_include']);
?>
