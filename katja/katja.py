#!/usr/bin/env python


"""
Katja, a Gtk Subversion client.
"""


VERSION = "0.1"
DATE = "2005/11/09"

GLADEFILE = "katja.glade"


from optparse import OptionParser
import gtk
import gtk.glade
#import pysvn


def actionCheckout(directory):

    CheckoutDialog()


class CheckoutDialog:


    def __init__(self):

        self.xml = gtk.glade.XML(GLADEFILE)
        self.window = self.xml.get_widget("windowCheckout")

        self.xml.get_widget('buttonCancel').connect('clicked', self.__on_cancel)

        self.window.show()


    def __on_cancel(self, w):
        self.window.destroy()


def main():

    """
    Parse command line options.
    """

    parser = OptionParser(usage = "usage: %prog <command> [options] [args]",
                          version = "Katja %s (%s)" % (VERSION, DATE),
                          description = "Katja is a graphical Subversion "
                          "client.")

    (options, args) = parser.parse_args()

    if len(args) < 1:
        parser.error("no command provided")

    actionCheckout("~")
    gtk.main()


if __name__ == "__main__":
    main()
