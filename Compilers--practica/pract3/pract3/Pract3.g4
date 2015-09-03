grammar Pract3;

@header {
  // import java packages
  import java.lang.String;
  import java.util.Set;
  import java.util.HashSet;
  import java.util.Arrays;
}

@members{
  // Keep a list of valid months, more explanation is given in the setMonth() method why
  // we choose this approach
  public final static Set validMonths = new HashSet(Arrays.asList(new String[] {
    "January", "Februari", "March", "April", "May", "June",
    "Juli", "August", "September", "October", "November", "December",
    "Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec",
    "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12"
  }));

  // Accession number of the records
  public static int rec_accession = 1; // Record counter

  // Information about the record being processed
  public static int current_ref_type = -1; // Type of the current record
  public static String current_year = "";  // Year of the current record
  public static String current_month = ""; // Month of the current record

  public static boolean labelSet;
  public static boolean authorSet;
  public static boolean titleSet;
  public static boolean yearSet;
  public static boolean publisherSet;
  public static boolean journalSet;
  public static boolean volumeSet;
  public static boolean numberSet;
  public static boolean pagesSet;
  public static boolean booktitleSet;

  // EndNote XML print methods
  public static void xmlout(String x, String y) { System.out.println("<"+x+">"+y+"</"+x+">");}
  public static void xmlb(String x)             { System.out.println("<" +x+">");}
  public static void xmle(String x)             { System.out.println("</"+x+">");}

  // Begins a record with an ID
  public static void printBeginRecord(int id) {
    // Start of a new record: unset all the varibales
    resetSetters();
    resetCurrent();

    // Start a new record entry
    xmlb("record");
    xmlout("rec-number", "" + rec_accession);
    rec_accession++;

    // Set the current ref type
    current_ref_type = id;
  }

  // Ends a record
  public static void printEndRecord() {
    // Now we've parsed all information, we'll have to do some additional work:
    //
    // Check wether all mandatory fields exist
    switch (current_ref_type) {
      case 6: // Book
        if (!(labelSet && authorSet && titleSet && yearSet && publisherSet)) {
          System.err.println("Please set all mandatory book fields");
        }
        break;
      case 17: // Article: special case with the (volume and number) or year here
        if (!(labelSet && authorSet && titleSet && journalSet && pagesSet && ((volumeSet && numberSet) || yearSet))) {
          System.err.println("Please set all mandatory article fields");
        }
        break;
      case 47: // Inproceedings
        if (!(labelSet && authorSet && titleSet && booktitleSet && yearSet)) {
          System.err.println("Please set all mandatory inproceedings fields");
        }
        break;
      default:
        // This should not happen
        System.err.println("This ref type was not recognized and should have been ignored" + current_ref_type);
    }

    // Print the dates
    printDates();

    xmle("record");
  }

  // Prints the ref-type
  public static void printLabel(String l) {
    System.out.println("<ref-type name=\"" + l + "\">" + current_ref_type + "</ref-type>");
  }

  // Prints the authors
  public static void printAuthors(String as) {
    String[] authors = as.split(" and | AND ");

    xmlb("contributors");
    xmlb("authors");

    for(String author : authors) {
        xmlout("author", author);
    }

    xmle("authors");
    xmle("contributors");
  }

  // Print the title
  public static void printTitle(String t) {
    xmlb("titles");
    xmlout("title", t);
    xmle("titles");
  }

  // Print the volume
  public static void printVolume(String v) {
    xmlout("volume", v);
  }

  // Print the number
  public static void printNumber(String n) {
    xmlout("number", n);
  }

  // Print the pages
  public static void printPages(String begin, String end) {
    int b = Integer.parseInt(begin);
    int e = Integer.parseInt(end);

    if (b > e) {
      System.err.println("Beginning of page range is bigger than ending.");
    } else {
      xmlout("pages", b + "--" + e);
    }
  }

  // Print the publisher
  public static void printPublisher(String p) {
    xmlout("publisher", p);
  }

  // Print the dates
  public static void printDates() {
    if(!"".equals(current_month) || !"".equals(current_year)) {
      xmlb("dates");
      if(!"".equals(current_year)) {
        xmlout("year", current_year);
      }
      if(!"".equals(current_month)) {
        xmlout("month", current_month);
      }
      xmle("dates");
    }
  }

  // Sets the year variable
  public static void setYear(String y) {
    yearSet = true;
    current_year = y;
  }

  // Sets the month variable
  // This needs some explanation: It should be possible to check the validity of
  // the formatting of the months in the language by checking if the value is one of
  // January .. December, Jan .. Dec or 1..12. But this approach prohibited two things:
  // If the month was misspelled (Ian instead of Jan for example), it wouldn't trigger
  // any error as it matched the ig_field (which ignores fields who shouldn't be in the
  // BibTex type. So it was not possible to trigger a custom error.
  // Instead, we'll match any WORD or NUMBER, parse it within Java and trigger an error
  // if the value isn't an allowed value.
  public static void setMonth(String m) {
    // If the validMonths set contains m, all is good, proceed:
    if(validMonths.contains(m)) {
      current_month = m;
    } else { // Else, find out which format the user used and trigger an appropriate warning
      // Check if we have a number
      int month_number;
      try {
        month_number = Integer.parseInt(m);
      } catch(NumberFormatException e) {
        // We don't have a number, so it's probably a string:
        if(m.length() == 3) { // Did the user mistype a 3-letter abbreviation?
          System.err.println("It seems like you entered a wrong 3-letter abbreviation. Please use "
                           + "one of the following: Jan, Feb, Mar, Apr, May, Jun, Jul, Aug, Sep, Oct, Nov, Dec. "
                           + "Full month names and numbers (1..12) are also allowed.");
        } else { // Or did he perhaps mistype the full name?
          System.err.println("It seems like you entered an unexisting month name. "
                           + "Abbreviated month names and numbers (1..12) are also allowed.");
        }
        return;
      }
      // We have a number, but why is it wrong?
      System.err.println("Please provide a valid number for the month field between 1 and 12. "
                      + "Full month names and 3-letter abbreviatons are also allowed.");
    }
  }

  // Set and unset the set variables methods
  public static void setLabel()     { labelSet     = true; }
  public static void setAuthor()    { authorSet    = true; }
  public static void setTitle()     { titleSet     = true; }
  public static void setPublisher() { publisherSet = true; }
  public static void setJournal()   { journalSet   = true; }
  public static void setVolume()    { volumeSet    = true; }
  public static void setNumber()    { numberSet    = true; }
  public static void setPages()     { pagesSet     = true; }
  public static void setBooktitle() { booktitleSet = true; }

  public static void resetSetters() {
    labelSet     = false;
    authorSet    = false;
    titleSet     = false;
    yearSet      = false;
    publisherSet = false;
    volumeSet    = false;
    numberSet    = false;
    journalSet   = false;
    pagesSet     = false;
    booktitleSet = false;
  }

  // Reset the current variables
  public static void resetCurrent() {
    current_ref_type = -1;
    current_year = "";
    current_month = "";
  }
}

// implement your LL(1) grammar
// parser should skip 'unknown' bibtex entries, i.e. don't generate EndNote output
//                    'unknown' fields

bibtex
  @init{System.out.println("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\r\n<xml>\r\n<records>");}
  @after{System.out.println("</records>\r\n</xml>");}
  : entry* EOF
  ;


// Lexer rules
// README: capital words are "terminals", non-capital are intermediary definitions

WS     : [ \t\n\r]+ -> channel(HIDDEN) ;

// Common
string : WORD (WORD)*;
address : string (FS string)*;

// Entries
entry : (book | article | inproceedings | undefined);

// Type definitions
book          : {printBeginRecord(6);}  BOOK_KEY          book_type_value          {printEndRecord();};
article       : {printBeginRecord(17);} ARTICLE_KEY       article_type_value       {printEndRecord();};
inproceedings : {printBeginRecord(47);} INPROCEEDINGS_KEY inproceedings_type_value {printEndRecord();};
undefined     : UNDEFINED_KEY ig_type_value;

// Common field definitions
book_type_value : LB  l=WORD {setLabel(); printLabel($l.text);} FS book_fields RB
                | LCB l=WORD {setLabel(); printLabel($l.text);} FS book_fields RCB
                ;
book_fields     : book_field (FS book_field)*;
book_field      : author_field | title_field | year_field | publisher_field | ig_field;

article_type_value : LB  l=WORD {setLabel(); printLabel($l.text);} FS article_fields RB
                   | LCB l=WORD {setLabel(); printLabel($l.text);} FS article_fields RCB
                   ;
article_fields     : article_field (FS article_field)*;
article_field      : author_field | title_field | journal_field | pages_field
                   | volume_field | number_field | year_field | ig_field
                   ;

inproceedings_type_value : LB  l=WORD {setLabel(); printLabel($l.text);} FS inproceedings_fields RB
                         | LCB l=WORD {setLabel(); printLabel($l.text);} FS inproceedings_fields RCB
                         ;
inproceedings_fields     : inproceedings_field (FS inproceedings_field)*;
inproceedings_field      : author_field | title_field | booktitle_field | year_field
                         | month_field | pages_field | ig_field
                         ;

// Ignored field definitions
ig_type_value : LB WORD FS ig_fields RB
              | LCB WORD FS ig_fields RCB
              ;
ig_fields     : ig_field (FS ig_field)*;
ig_field      : (AUTHOR_KEY | TITLE_KEY | PUBLISHER_KEY | JOURNAL_KEY | PAGES_KEY
                | VOLUME_KEY | NUMBER_KEY | YEAR_KEY | MONTH_KEY | PAGES_KEY
                | ISSN_KEY | DOI_KEY | ADDRESS_KEY | URL_KEY | BOOKTITLE_KEY)
                EQ any_value;

// Specific field definitions
author_field    : AUTHOR_KEY EQ text_value     {setAuthor();    printAuthors($text_value.text);};
title_field     : TITLE_KEY EQ text_value      {setTitle();     printTitle($text_value.text);};
publisher_field : PUBLISHER_KEY EQ text_value  {setPublisher(); printPublisher($text_value.text);};
pages_field     : PAGES_KEY EQ numeric_range   {setPages();     printPages($numeric_range.begin, $numeric_range.end);};
volume_field    : VOLUME_KEY EQ numeric_value  {setVolume();    printVolume($numeric_value.number);};
number_field    : NUMBER_KEY EQ numeric_value  {setNumber();    printNumber($numeric_value.number);};
journal_field   : JOURNAL_KEY EQ text_value    {setJournal();};
booktitle_field : BOOKTITLE_KEY EQ text_value  {setBooktitle();};
year_field      : YEAR_KEY EQ numeric_value    {setYear($numeric_value.number);};
month_field     : MONTH_KEY EQ month_value     {setMonth($month_value.text);};
// Unused (but they still need to be parsed) fields
issn_field      : ISSN_KEY EQ issn_range;
doi_field       : DOI_KEY EQ text_value;
address_field   : ADDRESS_KEY EQ address_value;
url_field       : URL_KEY  EQ text_value;

// Field value definition
any_value : text_value | numeric_value | month_value | numeric_range | issn_range | address_value;

text_value returns [String text]
              : QM string QM {$text = $string.text;}
              | LCB string RCB {$text = $string.text;}
              ;

numeric_value returns [String number]
              : QM NUMBER QM {$number = $NUMBER.text;}
              | LCB NUMBER RCB {$number = $NUMBER.text;}
              | NUMBER {$number = $NUMBER.text;}
              ;

month_value returns [String text]
              : QM month QM {$text = $month.text;}
              | LCB month RCB {$text = $month.text;}
              | NUMBER {$text = $NUMBER.text;}
              ;
month : NUMBER | WORD;

numeric_range returns [String begin, String end]
              : QM l=NUMBER RS RS r=NUMBER QM {$begin = $l.text; $end = $r.text;}
              | LCB l=NUMBER RS RS r=NUMBER RCB {$begin = $l.text; $end = $r.text;}
              ;

issn_range returns [String begin, String end]
              : QM l=NUMBER RS r=NUMBER QM {$begin = $l.text; $end = $r.text;}
              | LCB l=NUMBER RS r=NUMBER RCB {$begin = $l.text; $end = $r.text;}
              ;

address_value returns [String val]
              : QM address QM {$val = $address.text;}
              | LCB address RCB {$val = $address.text;}
              ;

// Type key definitions
BOOK_KEY          : '@book';
ARTICLE_KEY       : '@article';
INPROCEEDINGS_KEY : '@inproceedings';
UNDEFINED_KEY     : '@' ('a'..'z')+;

// Field keys definition
AUTHOR_KEY    : 'author';
TITLE_KEY     : 'title';
YEAR_KEY      : 'year';
PUBLISHER_KEY : 'publisher';
JOURNAL_KEY   : 'journal';
PAGES_KEY     : 'pages';
VOLUME_KEY    : 'volume';
NUMBER_KEY    : 'number';
MONTH_KEY     : 'month';
// Unused (but they still need to be parsed) fields
ISSN_KEY      : 'issn';
DOI_KEY       : 'doi';
ADDRESS_KEY   : 'address';
URL_KEY       : 'url';
BOOKTITLE_KEY : 'booktitle';

// Symbols
FS  : ','; // field seperator
RS  : '-'; // range seperator
EQ  : '='; // equality symbol
QM  : '"'; // equality symbol
LB  : '('; // left bracket
RB  : ')'; // right bracket
LCB : '{'; // left curly bracket
RCB : '}'; // right curly bracket

// Common
NUMBER    : ('0'..'9')+;
WORD      : ('a'..'z' | 'A'..'Z') ('a'..'z' | 'A'..'Z' | '0'..'9' | '.' | '-' | '/' | ':' | '~')*; // also allow URL characters . :  / - and the month seperator
