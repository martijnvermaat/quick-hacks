import gtk
import gtk.glade
#import pysvn


GLADEFILE = "/usr/lib/nautilus/extensions-1.0/python/subversion.glade"


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


if __name__ == "__main__":
    actionCheckout("~")
    gtk.main()
