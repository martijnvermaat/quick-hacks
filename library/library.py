#!/usr/bin/python


NAME = "Library"
VERSION = "0.1"
GLADE = "library.glade"


import sys
import inspect

from Ft.Lib import Uri
from Ft.Xml import InputSource
from Ft.Xml.Domlette import NonvalidatingReader
from Ft.Xml.XPath import Compile, Evaluate
from Ft.Xml.XPath.Context import Context
from Ft.Xml.Xvif import RelaxNgValidator

import pygtk
pygtk.require("2.0")
import gtk.glade
import gnome
import gobject


VALIDATION_SCHEMA = """<?xml version="1.0" encoding="UTF-8"?>
 
<element name="library" xmlns="http://relaxng.org/ns/structure/1.0">
    <zeroOrMore>
        <element name="item">
            <interleave>
                <element name="title">
                    <text />
                </element>
                <element name="authors">
                    <oneOrMore>
                        <element name="author">
                            <text />
                        </element>
                    </oneOrMore>
                </element>
                <element name="date">
                    <text />
                </element>
                <element name="type">
                    <text />
                </element>
                <element name="language">
                    <text />
                </element>
                <optional>
                    <element name="locations">
                        <interleave>
                            <optional>
                                <element name="physically">
                                    <text />
                                </element>
                            </optional>
                            <optional>
                                <element name="url">
                                    <text />
                                </element>
                            </optional>
                        </interleave>
                    </element>
                </optional>
            </interleave>
        </element>
    </zeroOrMore>
</element>
"""


def fileRead(filename, attrib):
    myFile = open(filename, attrib)
    contents = myFile.read()
    myFile.close()
    return contents


def cleanup():
    libxml2.relaxNGCleanupTypes()
    libxml2.cleanupParser()
    if libxml2.debugMemory(1) != 0:
        print "Memory leaked %d bytes" % libxml2.debugMemory(1)
        libxml2.dumpMemory()


class InvalidLibraryException(Exception):
    def __init__(self, filename):
        Exception.__init__(self)
        self.filename = filename


class LibraryList:

    COLUMN_POPUP = 4

    column_names = ['Title',
                    'Author(s)',
                    'Type',
                    'Language']

    def __init__(self, glade):
        self.widget = glade.get_widget("treeview")

        args = [gobject.TYPE_STRING] * len(self.column_names)
        args.append(gobject.TYPE_OBJECT)
        args.append(gobject.TYPE_PYOBJECT)
        self.model = apply(gtk.ListStore, args)
        self.sortModel = gtk.TreeModelSort(self.model)
        self.sortModel.set_sort_column_id(0, gtk.SORT_ASCENDING)
        self.widget.set_model(self.sortModel)

        renderer = gtk.CellRendererText()
        for name in self.column_names:
            column = gtk.TreeViewColumn(name,
                                        renderer,
                                        text=self.column_names.index(name))
            column.set_sort_column_id(self.column_names.index(name))
            column.set_resizable(True)
            column.set_sizing(gtk.TREE_VIEW_COLUMN_GROW_ONLY)
            self.widget.append_column(column)

        self.add_popup()

    def add_popup(self):
        popup_menu_items = (
            ("/_Refresh", None, self.menu, 0, "<Item>"),
            ("/_Alternating row colors", None, self.on_toggle_row_colors, 0, "<Item>"),
            ("/sep", None, None, 0, "<Separator>"),
            ("/_Remove", None, self.menu, 0, "<Item>"))

        item_factory = gtk.ItemFactory(gtk.Menu, '<list_popup>') # use gtk.UIManager instead
        item_factory.create_items(popup_menu_items)
        self.popup_menu = item_factory.get_widget('<list_popup>')
        self.widget.connect("popup-menu", self.on_popup_menu)
        self.widget.connect("button_press_event", self.on_button_press_event)

    def menu(self, *args):
        print "Menu!!!!"

    def on_toggle_row_colors(self, *args):
        self.widget.set_rules_hint(not(self.widget.get_rules_hint()))

    def on_popup_menu(self, *args):
        model, iter = self.widget.get_selection().get_selected()
        popup = model.get_model()[model.get_path(iter)][self.COLUMN_POPUP]
        popup.popup(None, None, None, 0, 0)
        return 1

    def on_button_press_event(self, treeview, event):
        if event.button == 3:
            x = int(event.x)
            y = int(event.y)
            time = gtk.get_current_event_time()
            path = treeview.get_path_at_pos(x, y)
            if path is None:
                return 1
            path, col, cellx, celly = path
            treeview.grab_focus()
            treeview.set_cursor( path, col, 0)
            model, iter = treeview.get_selection().get_selected()
            popup = model.get_model()[model.get_path(iter)][self.COLUMN_POPUP]
            popup.popup(None, None, None, event.button, time)
            return 1

    def addItem(self, item):
        iter = self.model.append()
        self.model.set(iter, 0, item['title'])
        self.model.set(iter, 1, "\n".join(item['authors']))
        self.model.set(iter, 2, item['type'])
        self.model.set(iter, 3, item['language'])
        self.model.set(iter, self.COLUMN_POPUP, self.popup_menu)
        self.model.set(iter, 5, item)

    def loadFromFile(self, filename):
        #rngParser = libxml2.relaxNGNewMemParserCtxt(VALIDATION_SCHEMA, len(VALIDATION_SCHEMA))
        #rngContext = rngParser.relaxNGParse().relaxNGNewValidCtxt()

        #file = fileRead(filename, 'r')
        #doc = libxml2.parseDoc(file)

        #if doc.relaxNGValidateDoc(rngContext) != 0:
        #    raise InvalidLibraryException(filename)

        #for item in doc.xpathEval('/library/item'):
        #    self.addItem({'authors':  map(lambda x: x.content, item.xpathEval('authors/author')),
        #                  'title':    item.xpathEval('title')[0].content,
        #                  'type':     item.xpathEval('type')[0].content,
        #                  'date':     item.xpathEval('date')[0].content,
        #                  'language': item.xpathEval('language')[0].content})

        factory = InputSource.DefaultFactory

        schema = factory.fromString(VALIDATION_SCHEMA)
        validator = RelaxNgValidator(schema)

        file = Uri.OsPathToUri(filename, attemptAbsolute=1)

        # validate file
        if not(validator.isValid(factory.fromUri(file))):
            raise InvalidLibraryException(filename)

        doc = NonvalidatingReader.parse(factory.fromUri(file))

        # read items from document
        for item in doc.xpath('/library/item'):
            self.addItem({'authors':  map(lambda x: x.childNodes[0].nodeValue.strip(), item.xpath('authors/author')),
                          'title':    item.xpath('title')[0].childNodes[0].nodeValue.strip(),
                          'type':     item.xpath('type')[0].childNodes[0].nodeValue.strip(),
                          'date':     item.xpath('date')[0].childNodes[0].nodeValue.strip(),
                          'language': item.xpath('language')[0].childNodes[0].nodeValue.strip()})


class LibraryWindow:

    def __init__(self, glade, doc=None):
        self.widget = glade.get_widget('window')
        self.about = glade.get_widget('about')
        
        self.about.set_property('name', NAME)
        self.about.set_property('version', VERSION)

        self.libraryList = LibraryList(glade)

        if doc:
            try:
                self.libraryList.loadFromFile(doc)
            except InvalidLibraryException, e:
                print "Invalid library: %s" % e.filename

        # autoconnect signal methods to handlers
        dict = {}
        for name, member in inspect.getmembers(self):
            dict[name] = member
        glade.signal_autoconnect(dict)

    def close(self, *args):
        self.widget.destroy()
        gtk.main_quit()
        return True

    on_window_delete_event = close
    on_quit_activate = close

    def on_about_activate(self, *args):
        self.about.show()

    def on_open_activate(self, *args):
        chooser = gtk.FileChooserDialog(title="Open library",
                                        action=gtk.FILE_CHOOSER_ACTION_OPEN,
                                        buttons=(gtk.STOCK_CANCEL,
                                                 gtk.RESPONSE_CANCEL,
                                                 gtk.STOCK_OPEN,gtk.RESPONSE_OK))
        chooser.run()
        chooser.destroy()


def main(arguments):

    gnome.init(NAME, VERSION)
    glade = gtk.glade.XML(GLADE)

    if len(arguments) > 0:
        win = LibraryWindow(glade, arguments[0])
    else:
        win = LibraryWindow(glade)

    gtk.main()


if __name__ == '__main__':
    main(sys.argv[1:])
