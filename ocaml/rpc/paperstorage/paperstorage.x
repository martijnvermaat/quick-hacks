/* XDR Data Description for a Paper Storage Protocol */


/* Constant definitions */

const MAX_AUTHOR_LENGTH  = 255;
const MAX_TITLE_LENGTH   = 255;
const MAX_MESSAGE_LENGTH = 255;


/* Basic datatypes */

enum status {
    STATUS_SUCCESS = 0,
    STATUS_ERROR   = 1
};

typedef opaque data <>;

struct document {
    int    *number                       ;
    string  author   <MAX_AUTHOR_LENGTH> ;
    string  title    <MAX_TITLE_LENGTH>  ;
    data   *content                      ;
};

typedef struct document_node *document_list;

struct document_node {
    document      item;
    document_list next;
};

typedef string message <MAX_MESSAGE_LENGTH>;


/* ADD_PROC input and output types */

struct add_in {
    document paper;
};

union add_out switch(status result) {
    case STATUS_SUCCESS:
        document paper;
    case STATUS_ERROR:
        message reason;
};


/* GET_PROC input and output types */

struct get_in {
    int number;
    int complete;
};

union get_out switch(status result) {
    case STATUS_SUCCESS:
        document paper;
    case STATUS_ERROR:
        message reason;
};


/* LIST_PROC input and output types */

/* input type is void */

struct list_out {
    document_list papers;
};


/* Program and procedures declaration */

program PAPERSTORAGE_PROG {
    version PAPERSTORAGE_VERS {
        add_out  ADD_PROC(add_in) = 1;
        get_out  GET_PROC(get_in) = 2;
        list_out LIST_PROC(void)  = 3;
    } = 1;
} = 0x3234763;
