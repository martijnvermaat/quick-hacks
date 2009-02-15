// ==UserScript==
// @name          Nu Compact
// @namespace     http://www.cs.vu.nl/~mvermaat/
// @description   Remove pictures from frontpage stories keeping just links
// @include       http://www.nu.nl/
// ==/UserScript==


/*
    Nu Compact

    Version: 0.3.0, 2009-02-15

    http://www.cs.vu.nl/~mvermaat/greasemonkey

    Martijn Vermaat, mvermaat@cs.vu.nl


    Pictures added to stories on nu.nl have nothing to do with
    the stories most of the time. They occupy a lot of space
    and prevent me from having the entire frontpage in one
    screen.
    Nu Compact removes the pictures on the frontpage, by
    transforming stories with pictures to plain links. Also, I
    know what the current date is and the nu.nl logo takes up
    too much space, so Nu Compact removes them.


    Known bugs:
    * We should also remove the stupid column soundbites on
      the right side of the frontpage.
    * We should render the entire page blank and suggest some
      other source for news.


    Changelog

    2009-02-15 - 0.3.0
    * Adapted to new nu.nl layout

    2008-10-18 - 0.2.2
    * Added video section

    2007-04-03 - 0.2.1
    * Also remove logo and date
    * Added known bugs

    2007-04-03 - 0.2
    * Adapted to new nu.nl layout

    2005-05-29 - 0.1
    * Initial version


    Nu Compact is Open Source and licensed under the new
    BSD License, found at:
    http://www.opensource.org/licenses/bsd-license.php
*/



/*
    Wrap the whole thing in an anonymous function to avoid
    nameclashes with existing Javascript.
*/
(function() {


function getLinksFromPicturizedStories() {

    var stories, story, link, links, newLink;

    // Find containers for picturized stories
    stories = document.evaluate("//div[contains(@class,'subarticle') or contains(@class, 'leadarticle')]",
                                document,
                                null,
                                XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE,
                                null);

    for (var i = 0; i < stories.snapshotLength; i++) {

        story = stories.snapshotItem(i);

        // Get color class
        cclass = story.className.split(' ').pop();

        // The link containing url and title of story
        link = document.evaluate('.//h2/a',
                                 story,
                                 null,
                                 XPathResult.FIRST_ORDERED_NODE_TYPE,
                                 null).singleNodeValue;

        // Placeholder for plain links to stories
        links = document.evaluate('./following::div[1]//ul',
                                  story,
                                  null,
                                  XPathResult.FIRST_ORDERED_NODE_TYPE,
                                  null).singleNodeValue;

        // Create new link container li
        newLink = document.createElement('li');
        newLink.className = cclass;

        // Copy the link
        newLink.insertBefore(link, null);

        // Add plain link for this story
        links.insertBefore(newLink, links.firstChild);

    }

}


function removeUselessThings() {

    var thing, things;

    things = document.evaluate("id('feeds adblock_h masthead')|//div[contains(@class,'subarticle') or contains(@class, 'leadarticle')]",
                                document,
                                null,
                                XPathResult.UNORDERED_NODE_SNAPSHOT_TYPE,
                                null);

    for (var i = 0; i < things.snapshotLength; i++) {

        thing = things.snapshotItem(i);
        thing.parentNode.removeChild(thing);

    }

}


getLinksFromPicturizedStories();
removeUselessThings();


/*
    End of wrapper function (see top of script).
*/
})();
