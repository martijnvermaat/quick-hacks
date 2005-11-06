import os
import urllib
import gtk
import gtk.glade
import nautilus
#import pysvn


GLADEFILE = '/usr/lib/nautilus/extensions-1.0/python/test.glade'


class TestView:

    def __init__(self):
        self.xml = gtk.glade.XML(GLADEFILE)
        self.window = self.xml.get_widget('window1')
        self.window.show()


class SubversionMenu(nautilus.MenuProvider):

    def __init__(self):
        pass

    def _action(self, menu, file, window):
        TestView()
        os.spawnlp(os.P_NOWAIT, "beep")
        return

    def get_file_items(self, window, files):

        items = []

        #if len(files) != 1:
        #    return

        file = files[0]

        is_directory = file.is_directory()

        if file.get_uri_scheme() != 'file':
            return

        filename = urllib.unquote(file.get_uri()[7:])
        if is_directory and len(files) == 1:
            items = self.get_background_items(window, file)
        else:
            pass

        return items

    def get_background_items(self, window, file):

        if file.get_uri_scheme() != 'file':
            return

        filename = urllib.unquote(file.get_uri()[7:])
        items = []

        # Get version from archive
        item = nautilus.MenuItem('Subversion::dir_item',
                                 'Check out working copy',
                                 'Check out a working copy from a repository')
                                 #,'gtk-go-down')
        item.connect('activate', self._action, filename, window)
        items.append(item)

        return items
