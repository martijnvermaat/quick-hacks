=== Nginx Proxy Cache Purge ===
Contributors: jlevandowski
Tags: nginx, proxy, cache, purge
Requires at least: 3.0.1
Tested up to: 3.0.1
Stable tag: 0.9.4

Purges the nginx proxy cache when you publish or update a post or page.

== Description ==

Purges the nginx proxy cache when you publish or update a post or page.  The cache will be purged for the:

* Page or post you published or updated
* Front page of your site
* Posts page of your site (if enabled)
* Feed of your site
* Comments feed of your site

== Installation ==

Upload the Nginx Proxy Cache Purge plugin to your site, Activate it, and Enjoy!

== Frequently Asked Questions ==

= What are the server requirements? =

[Nginx reverse proxy cache](http://wiki.nginx.org/) running with the [ngx_cache_purge](http://labs.frickle.com/nginx_ngx_cache_purge/) module installed.  I have published instructions at: [http://johnlevandowski.com/2010/10/05/wordpress-nginx-proxy-cache/](http://johnlevandowski.com/2010/10/05/wordpress-nginx-proxy-cache/)

= How does this plugin work? =

After your publish or update a page or post this plugin creates a list or url's to purge.  For instance if the page is http://www.example.com/about/, the plugin creates a url of http://www.example.com/purge/about/.  After creating all the urls to purge, the plugin opens each of the urls.  It is critical that you have nginx configured with a location of /purge/.  You can manually purge a page by opening the purge url directly.

== Changelog ==

= 0.9.4 =
* Changed URL for instructions.

= 0.9.3 =
* Added html comment to show when page was created.  Useful in determining if page was delivered from cache and validating that cache was purged.

= 0.9.2 =
* No need to clear the posts page if it's not enabled.

= 0.9.1 =
* Removed curl dependancy.

= 0.9 =
* Initial Beta Release.