"""
Subversion
"""


VERSION = "0.1.1"
DATE = "2005/10/25"

GLADEFILE = "/usr/lib/nautilus/extensions-1.0/python/subversion.glade"


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

    parser = OptionParser(usage = "usage: %prog <subcommand> [options] "
                          "[args]",
                          version = "Subversion %s (%s)" % (VERSION, DATE),
                          description = "Subversion is a graphical client.")

    parser.add_option("-i", "--input", dest="input", metavar="FILE",
                      help="read FILE in Fasta format")
    parser.add_option("-w", "--width", dest="width", metavar="WIDTH",
                      type="int", help="find motif of width WIDTH")
    parser.add_option("-t", "--iterations", dest="iterations",
                      metavar="ITERATIONS", default=ITERATIONS_DEFAULT,
                      type="int", help="number of non-improving iterations "
                      "(default " + str(ITERATIONS_DEFAULT) + ")")
    parser.add_option("-p", "--pseudo", dest="pseudo", metavar="WEIGHT",
                      default=PSEUDOCOUNTS_WEIGHT_DEFAULT, type="float",
                      help="use WEIGHT for weight of pseudocounts (default " +
                      str(PSEUDOCOUNTS_WEIGHT_DEFAULT) + ")")
    parser.add_option("-s", "--phase-shifts", dest="shifts", metavar="SHIFTS",
                      default=PHASE_SHIFTS_DEFAULT, type="int",
                      help="detect phase shifts of width SHIFTS (default " +
                      str(PHASE_SHIFTS_DEFAULT) + ")")
    parser.add_option("-f", "--ps-frequency", dest="frequency",
                      metavar="FREQ", default=PS_FREQUENCY_DEFAULT,
                      type="int", help="if SHIFTS>0, detect phase shifts "
                      "every FREQ iterations (default " +
                      str(PS_FREQUENCY_DEFAULT) + ")")
    parser.add_option("-n", "--init-num-occurrences", dest="initoccurrences",
                      metavar="OCCURRENCES",
                      default=INIT_NUM_OCCURRENCES_DEFAULT, type="int",
                      help="number of base occurrences to use for initial "
                      "positions heuristic (default " +
                      str(INIT_NUM_OCCURRENCES_DEFAULT) + ")")
    parser.add_option("-v", "--init-pattern-width", dest="initwidth",
                      metavar="WIDTH", default=INIT_PATTERN_WIDTH_DEFAULT,
                      type="int", help="if OCCURRENCES>0, width of pattern "
                      "to use for initial positions heuristic (defaults to "
                      "value of --width)")
    parser.add_option("-c", "--cow", action="store_true", dest="cow",
                      default=False, help="display cow (not recommended)")

    (options, args) = parser.parse_args()


    actionCheckout("~")
    gtk.main()


if __name__ == "__main__":
    main()
