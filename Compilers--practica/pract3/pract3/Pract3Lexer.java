// Generated from Pract3.g4 by ANTLR 4.5

  // import java packages
  import java.lang.String;
  import java.util.Set;
  import java.util.HashSet;
  import java.util.Arrays;

import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class Pract3Lexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.5", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		WS=1, BOOK_KEY=2, ARTICLE_KEY=3, INPROCEEDINGS_KEY=4, UNDEFINED_KEY=5, 
		AUTHOR_KEY=6, TITLE_KEY=7, YEAR_KEY=8, PUBLISHER_KEY=9, JOURNAL_KEY=10, 
		PAGES_KEY=11, VOLUME_KEY=12, NUMBER_KEY=13, MONTH_KEY=14, ISSN_KEY=15, 
		DOI_KEY=16, ADDRESS_KEY=17, URL_KEY=18, BOOKTITLE_KEY=19, FS=20, RS=21, 
		EQ=22, QM=23, LB=24, RB=25, LCB=26, RCB=27, NUMBER=28, WORD=29;
	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	public static final String[] ruleNames = {
		"WS", "BOOK_KEY", "ARTICLE_KEY", "INPROCEEDINGS_KEY", "UNDEFINED_KEY", 
		"AUTHOR_KEY", "TITLE_KEY", "YEAR_KEY", "PUBLISHER_KEY", "JOURNAL_KEY", 
		"PAGES_KEY", "VOLUME_KEY", "NUMBER_KEY", "MONTH_KEY", "ISSN_KEY", "DOI_KEY", 
		"ADDRESS_KEY", "URL_KEY", "BOOKTITLE_KEY", "FS", "RS", "EQ", "QM", "LB", 
		"RB", "LCB", "RCB", "NUMBER", "WORD"
	};

	private static final String[] _LITERAL_NAMES = {
		null, null, "'@book'", "'@article'", "'@inproceedings'", null, "'author'", 
		"'title'", "'year'", "'publisher'", "'journal'", "'pages'", "'volume'", 
		"'number'", "'month'", "'issn'", "'doi'", "'address'", "'url'", "'booktitle'", 
		"','", "'-'", "'='", "'\"'", "'('", "')'", "'{'", "'}'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, "WS", "BOOK_KEY", "ARTICLE_KEY", "INPROCEEDINGS_KEY", "UNDEFINED_KEY", 
		"AUTHOR_KEY", "TITLE_KEY", "YEAR_KEY", "PUBLISHER_KEY", "JOURNAL_KEY", 
		"PAGES_KEY", "VOLUME_KEY", "NUMBER_KEY", "MONTH_KEY", "ISSN_KEY", "DOI_KEY", 
		"ADDRESS_KEY", "URL_KEY", "BOOKTITLE_KEY", "FS", "RS", "EQ", "QM", "LB", 
		"RB", "LCB", "RCB", "NUMBER", "WORD"
	};
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


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


	public Pract3Lexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "Pract3.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\2\37\u00e1\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31"+
		"\t\31\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\3\2\6\2?\n\2\r"+
		"\2\16\2@\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3"+
		"\4\3\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\6"+
		"\3\6\6\6e\n\6\r\6\16\6f\3\7\3\7\3\7\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3"+
		"\b\3\b\3\t\3\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\13"+
		"\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\r\3\r\3"+
		"\r\3\r\3\r\3\r\3\r\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\17\3\17\3\17\3"+
		"\17\3\17\3\17\3\20\3\20\3\20\3\20\3\20\3\21\3\21\3\21\3\21\3\22\3\22\3"+
		"\22\3\22\3\22\3\22\3\22\3\22\3\23\3\23\3\23\3\23\3\24\3\24\3\24\3\24\3"+
		"\24\3\24\3\24\3\24\3\24\3\24\3\25\3\25\3\26\3\26\3\27\3\27\3\30\3\30\3"+
		"\31\3\31\3\32\3\32\3\33\3\33\3\34\3\34\3\35\6\35\u00d7\n\35\r\35\16\35"+
		"\u00d8\3\36\3\36\7\36\u00dd\n\36\f\36\16\36\u00e0\13\36\2\2\37\3\3\5\4"+
		"\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37\21!\22"+
		"#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\65\34\67\359\36;\37\3\2\5\5"+
		"\2\13\f\17\17\"\"\4\2C\\c|\6\2/<C\\c|\u0080\u0080\u00e4\2\3\3\2\2\2\2"+
		"\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2"+
		"\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2"+
		"\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2"+
		"\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3\2\2\2"+
		"\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3\2\2\2\29\3\2\2\2\2;\3\2\2\2\3>\3\2\2"+
		"\2\5D\3\2\2\2\7J\3\2\2\2\tS\3\2\2\2\13b\3\2\2\2\rh\3\2\2\2\17o\3\2\2\2"+
		"\21u\3\2\2\2\23z\3\2\2\2\25\u0084\3\2\2\2\27\u008c\3\2\2\2\31\u0092\3"+
		"\2\2\2\33\u0099\3\2\2\2\35\u00a0\3\2\2\2\37\u00a6\3\2\2\2!\u00ab\3\2\2"+
		"\2#\u00af\3\2\2\2%\u00b7\3\2\2\2\'\u00bb\3\2\2\2)\u00c5\3\2\2\2+\u00c7"+
		"\3\2\2\2-\u00c9\3\2\2\2/\u00cb\3\2\2\2\61\u00cd\3\2\2\2\63\u00cf\3\2\2"+
		"\2\65\u00d1\3\2\2\2\67\u00d3\3\2\2\29\u00d6\3\2\2\2;\u00da\3\2\2\2=?\t"+
		"\2\2\2>=\3\2\2\2?@\3\2\2\2@>\3\2\2\2@A\3\2\2\2AB\3\2\2\2BC\b\2\2\2C\4"+
		"\3\2\2\2DE\7B\2\2EF\7d\2\2FG\7q\2\2GH\7q\2\2HI\7m\2\2I\6\3\2\2\2JK\7B"+
		"\2\2KL\7c\2\2LM\7t\2\2MN\7v\2\2NO\7k\2\2OP\7e\2\2PQ\7n\2\2QR\7g\2\2R\b"+
		"\3\2\2\2ST\7B\2\2TU\7k\2\2UV\7p\2\2VW\7r\2\2WX\7t\2\2XY\7q\2\2YZ\7e\2"+
		"\2Z[\7g\2\2[\\\7g\2\2\\]\7f\2\2]^\7k\2\2^_\7p\2\2_`\7i\2\2`a\7u\2\2a\n"+
		"\3\2\2\2bd\7B\2\2ce\4c|\2dc\3\2\2\2ef\3\2\2\2fd\3\2\2\2fg\3\2\2\2g\f\3"+
		"\2\2\2hi\7c\2\2ij\7w\2\2jk\7v\2\2kl\7j\2\2lm\7q\2\2mn\7t\2\2n\16\3\2\2"+
		"\2op\7v\2\2pq\7k\2\2qr\7v\2\2rs\7n\2\2st\7g\2\2t\20\3\2\2\2uv\7{\2\2v"+
		"w\7g\2\2wx\7c\2\2xy\7t\2\2y\22\3\2\2\2z{\7r\2\2{|\7w\2\2|}\7d\2\2}~\7"+
		"n\2\2~\177\7k\2\2\177\u0080\7u\2\2\u0080\u0081\7j\2\2\u0081\u0082\7g\2"+
		"\2\u0082\u0083\7t\2\2\u0083\24\3\2\2\2\u0084\u0085\7l\2\2\u0085\u0086"+
		"\7q\2\2\u0086\u0087\7w\2\2\u0087\u0088\7t\2\2\u0088\u0089\7p\2\2\u0089"+
		"\u008a\7c\2\2\u008a\u008b\7n\2\2\u008b\26\3\2\2\2\u008c\u008d\7r\2\2\u008d"+
		"\u008e\7c\2\2\u008e\u008f\7i\2\2\u008f\u0090\7g\2\2\u0090\u0091\7u\2\2"+
		"\u0091\30\3\2\2\2\u0092\u0093\7x\2\2\u0093\u0094\7q\2\2\u0094\u0095\7"+
		"n\2\2\u0095\u0096\7w\2\2\u0096\u0097\7o\2\2\u0097\u0098\7g\2\2\u0098\32"+
		"\3\2\2\2\u0099\u009a\7p\2\2\u009a\u009b\7w\2\2\u009b\u009c\7o\2\2\u009c"+
		"\u009d\7d\2\2\u009d\u009e\7g\2\2\u009e\u009f\7t\2\2\u009f\34\3\2\2\2\u00a0"+
		"\u00a1\7o\2\2\u00a1\u00a2\7q\2\2\u00a2\u00a3\7p\2\2\u00a3\u00a4\7v\2\2"+
		"\u00a4\u00a5\7j\2\2\u00a5\36\3\2\2\2\u00a6\u00a7\7k\2\2\u00a7\u00a8\7"+
		"u\2\2\u00a8\u00a9\7u\2\2\u00a9\u00aa\7p\2\2\u00aa \3\2\2\2\u00ab\u00ac"+
		"\7f\2\2\u00ac\u00ad\7q\2\2\u00ad\u00ae\7k\2\2\u00ae\"\3\2\2\2\u00af\u00b0"+
		"\7c\2\2\u00b0\u00b1\7f\2\2\u00b1\u00b2\7f\2\2\u00b2\u00b3\7t\2\2\u00b3"+
		"\u00b4\7g\2\2\u00b4\u00b5\7u\2\2\u00b5\u00b6\7u\2\2\u00b6$\3\2\2\2\u00b7"+
		"\u00b8\7w\2\2\u00b8\u00b9\7t\2\2\u00b9\u00ba\7n\2\2\u00ba&\3\2\2\2\u00bb"+
		"\u00bc\7d\2\2\u00bc\u00bd\7q\2\2\u00bd\u00be\7q\2\2\u00be\u00bf\7m\2\2"+
		"\u00bf\u00c0\7v\2\2\u00c0\u00c1\7k\2\2\u00c1\u00c2\7v\2\2\u00c2\u00c3"+
		"\7n\2\2\u00c3\u00c4\7g\2\2\u00c4(\3\2\2\2\u00c5\u00c6\7.\2\2\u00c6*\3"+
		"\2\2\2\u00c7\u00c8\7/\2\2\u00c8,\3\2\2\2\u00c9\u00ca\7?\2\2\u00ca.\3\2"+
		"\2\2\u00cb\u00cc\7$\2\2\u00cc\60\3\2\2\2\u00cd\u00ce\7*\2\2\u00ce\62\3"+
		"\2\2\2\u00cf\u00d0\7+\2\2\u00d0\64\3\2\2\2\u00d1\u00d2\7}\2\2\u00d2\66"+
		"\3\2\2\2\u00d3\u00d4\7\177\2\2\u00d48\3\2\2\2\u00d5\u00d7\4\62;\2\u00d6"+
		"\u00d5\3\2\2\2\u00d7\u00d8\3\2\2\2\u00d8\u00d6\3\2\2\2\u00d8\u00d9\3\2"+
		"\2\2\u00d9:\3\2\2\2\u00da\u00de\t\3\2\2\u00db\u00dd\t\4\2\2\u00dc\u00db"+
		"\3\2\2\2\u00dd\u00e0\3\2\2\2\u00de\u00dc\3\2\2\2\u00de\u00df\3\2\2\2\u00df"+
		"<\3\2\2\2\u00e0\u00de\3\2\2\2\7\2@f\u00d8\u00de\3\2\3\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}