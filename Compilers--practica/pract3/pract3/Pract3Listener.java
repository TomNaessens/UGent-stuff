// Generated from Pract3.g4 by ANTLR 4.5

  // import java packages
  import java.lang.String;
  import java.util.Set;
  import java.util.HashSet;
  import java.util.Arrays;

import org.antlr.v4.runtime.misc.NotNull;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link Pract3Parser}.
 */
public interface Pract3Listener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#bibtex}.
	 * @param ctx the parse tree
	 */
	void enterBibtex(Pract3Parser.BibtexContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#bibtex}.
	 * @param ctx the parse tree
	 */
	void exitBibtex(Pract3Parser.BibtexContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#string}.
	 * @param ctx the parse tree
	 */
	void enterString(Pract3Parser.StringContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#string}.
	 * @param ctx the parse tree
	 */
	void exitString(Pract3Parser.StringContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#address}.
	 * @param ctx the parse tree
	 */
	void enterAddress(Pract3Parser.AddressContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#address}.
	 * @param ctx the parse tree
	 */
	void exitAddress(Pract3Parser.AddressContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#entry}.
	 * @param ctx the parse tree
	 */
	void enterEntry(Pract3Parser.EntryContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#entry}.
	 * @param ctx the parse tree
	 */
	void exitEntry(Pract3Parser.EntryContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#book}.
	 * @param ctx the parse tree
	 */
	void enterBook(Pract3Parser.BookContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#book}.
	 * @param ctx the parse tree
	 */
	void exitBook(Pract3Parser.BookContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#article}.
	 * @param ctx the parse tree
	 */
	void enterArticle(Pract3Parser.ArticleContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#article}.
	 * @param ctx the parse tree
	 */
	void exitArticle(Pract3Parser.ArticleContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#inproceedings}.
	 * @param ctx the parse tree
	 */
	void enterInproceedings(Pract3Parser.InproceedingsContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#inproceedings}.
	 * @param ctx the parse tree
	 */
	void exitInproceedings(Pract3Parser.InproceedingsContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#undefined}.
	 * @param ctx the parse tree
	 */
	void enterUndefined(Pract3Parser.UndefinedContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#undefined}.
	 * @param ctx the parse tree
	 */
	void exitUndefined(Pract3Parser.UndefinedContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#book_type_value}.
	 * @param ctx the parse tree
	 */
	void enterBook_type_value(Pract3Parser.Book_type_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#book_type_value}.
	 * @param ctx the parse tree
	 */
	void exitBook_type_value(Pract3Parser.Book_type_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#book_fields}.
	 * @param ctx the parse tree
	 */
	void enterBook_fields(Pract3Parser.Book_fieldsContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#book_fields}.
	 * @param ctx the parse tree
	 */
	void exitBook_fields(Pract3Parser.Book_fieldsContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#book_field}.
	 * @param ctx the parse tree
	 */
	void enterBook_field(Pract3Parser.Book_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#book_field}.
	 * @param ctx the parse tree
	 */
	void exitBook_field(Pract3Parser.Book_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#article_type_value}.
	 * @param ctx the parse tree
	 */
	void enterArticle_type_value(Pract3Parser.Article_type_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#article_type_value}.
	 * @param ctx the parse tree
	 */
	void exitArticle_type_value(Pract3Parser.Article_type_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#article_fields}.
	 * @param ctx the parse tree
	 */
	void enterArticle_fields(Pract3Parser.Article_fieldsContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#article_fields}.
	 * @param ctx the parse tree
	 */
	void exitArticle_fields(Pract3Parser.Article_fieldsContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#article_field}.
	 * @param ctx the parse tree
	 */
	void enterArticle_field(Pract3Parser.Article_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#article_field}.
	 * @param ctx the parse tree
	 */
	void exitArticle_field(Pract3Parser.Article_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#inproceedings_type_value}.
	 * @param ctx the parse tree
	 */
	void enterInproceedings_type_value(Pract3Parser.Inproceedings_type_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#inproceedings_type_value}.
	 * @param ctx the parse tree
	 */
	void exitInproceedings_type_value(Pract3Parser.Inproceedings_type_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#inproceedings_fields}.
	 * @param ctx the parse tree
	 */
	void enterInproceedings_fields(Pract3Parser.Inproceedings_fieldsContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#inproceedings_fields}.
	 * @param ctx the parse tree
	 */
	void exitInproceedings_fields(Pract3Parser.Inproceedings_fieldsContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#inproceedings_field}.
	 * @param ctx the parse tree
	 */
	void enterInproceedings_field(Pract3Parser.Inproceedings_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#inproceedings_field}.
	 * @param ctx the parse tree
	 */
	void exitInproceedings_field(Pract3Parser.Inproceedings_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#ig_type_value}.
	 * @param ctx the parse tree
	 */
	void enterIg_type_value(Pract3Parser.Ig_type_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#ig_type_value}.
	 * @param ctx the parse tree
	 */
	void exitIg_type_value(Pract3Parser.Ig_type_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#ig_fields}.
	 * @param ctx the parse tree
	 */
	void enterIg_fields(Pract3Parser.Ig_fieldsContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#ig_fields}.
	 * @param ctx the parse tree
	 */
	void exitIg_fields(Pract3Parser.Ig_fieldsContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#ig_field}.
	 * @param ctx the parse tree
	 */
	void enterIg_field(Pract3Parser.Ig_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#ig_field}.
	 * @param ctx the parse tree
	 */
	void exitIg_field(Pract3Parser.Ig_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#author_field}.
	 * @param ctx the parse tree
	 */
	void enterAuthor_field(Pract3Parser.Author_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#author_field}.
	 * @param ctx the parse tree
	 */
	void exitAuthor_field(Pract3Parser.Author_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#title_field}.
	 * @param ctx the parse tree
	 */
	void enterTitle_field(Pract3Parser.Title_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#title_field}.
	 * @param ctx the parse tree
	 */
	void exitTitle_field(Pract3Parser.Title_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#publisher_field}.
	 * @param ctx the parse tree
	 */
	void enterPublisher_field(Pract3Parser.Publisher_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#publisher_field}.
	 * @param ctx the parse tree
	 */
	void exitPublisher_field(Pract3Parser.Publisher_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#pages_field}.
	 * @param ctx the parse tree
	 */
	void enterPages_field(Pract3Parser.Pages_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#pages_field}.
	 * @param ctx the parse tree
	 */
	void exitPages_field(Pract3Parser.Pages_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#volume_field}.
	 * @param ctx the parse tree
	 */
	void enterVolume_field(Pract3Parser.Volume_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#volume_field}.
	 * @param ctx the parse tree
	 */
	void exitVolume_field(Pract3Parser.Volume_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#number_field}.
	 * @param ctx the parse tree
	 */
	void enterNumber_field(Pract3Parser.Number_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#number_field}.
	 * @param ctx the parse tree
	 */
	void exitNumber_field(Pract3Parser.Number_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#journal_field}.
	 * @param ctx the parse tree
	 */
	void enterJournal_field(Pract3Parser.Journal_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#journal_field}.
	 * @param ctx the parse tree
	 */
	void exitJournal_field(Pract3Parser.Journal_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#booktitle_field}.
	 * @param ctx the parse tree
	 */
	void enterBooktitle_field(Pract3Parser.Booktitle_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#booktitle_field}.
	 * @param ctx the parse tree
	 */
	void exitBooktitle_field(Pract3Parser.Booktitle_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#year_field}.
	 * @param ctx the parse tree
	 */
	void enterYear_field(Pract3Parser.Year_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#year_field}.
	 * @param ctx the parse tree
	 */
	void exitYear_field(Pract3Parser.Year_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#month_field}.
	 * @param ctx the parse tree
	 */
	void enterMonth_field(Pract3Parser.Month_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#month_field}.
	 * @param ctx the parse tree
	 */
	void exitMonth_field(Pract3Parser.Month_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#issn_field}.
	 * @param ctx the parse tree
	 */
	void enterIssn_field(Pract3Parser.Issn_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#issn_field}.
	 * @param ctx the parse tree
	 */
	void exitIssn_field(Pract3Parser.Issn_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#doi_field}.
	 * @param ctx the parse tree
	 */
	void enterDoi_field(Pract3Parser.Doi_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#doi_field}.
	 * @param ctx the parse tree
	 */
	void exitDoi_field(Pract3Parser.Doi_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#address_field}.
	 * @param ctx the parse tree
	 */
	void enterAddress_field(Pract3Parser.Address_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#address_field}.
	 * @param ctx the parse tree
	 */
	void exitAddress_field(Pract3Parser.Address_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#url_field}.
	 * @param ctx the parse tree
	 */
	void enterUrl_field(Pract3Parser.Url_fieldContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#url_field}.
	 * @param ctx the parse tree
	 */
	void exitUrl_field(Pract3Parser.Url_fieldContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#any_value}.
	 * @param ctx the parse tree
	 */
	void enterAny_value(Pract3Parser.Any_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#any_value}.
	 * @param ctx the parse tree
	 */
	void exitAny_value(Pract3Parser.Any_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#text_value}.
	 * @param ctx the parse tree
	 */
	void enterText_value(Pract3Parser.Text_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#text_value}.
	 * @param ctx the parse tree
	 */
	void exitText_value(Pract3Parser.Text_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#numeric_value}.
	 * @param ctx the parse tree
	 */
	void enterNumeric_value(Pract3Parser.Numeric_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#numeric_value}.
	 * @param ctx the parse tree
	 */
	void exitNumeric_value(Pract3Parser.Numeric_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#month_value}.
	 * @param ctx the parse tree
	 */
	void enterMonth_value(Pract3Parser.Month_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#month_value}.
	 * @param ctx the parse tree
	 */
	void exitMonth_value(Pract3Parser.Month_valueContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#month}.
	 * @param ctx the parse tree
	 */
	void enterMonth(Pract3Parser.MonthContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#month}.
	 * @param ctx the parse tree
	 */
	void exitMonth(Pract3Parser.MonthContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#numeric_range}.
	 * @param ctx the parse tree
	 */
	void enterNumeric_range(Pract3Parser.Numeric_rangeContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#numeric_range}.
	 * @param ctx the parse tree
	 */
	void exitNumeric_range(Pract3Parser.Numeric_rangeContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#issn_range}.
	 * @param ctx the parse tree
	 */
	void enterIssn_range(Pract3Parser.Issn_rangeContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#issn_range}.
	 * @param ctx the parse tree
	 */
	void exitIssn_range(Pract3Parser.Issn_rangeContext ctx);
	/**
	 * Enter a parse tree produced by {@link Pract3Parser#address_value}.
	 * @param ctx the parse tree
	 */
	void enterAddress_value(Pract3Parser.Address_valueContext ctx);
	/**
	 * Exit a parse tree produced by {@link Pract3Parser#address_value}.
	 * @param ctx the parse tree
	 */
	void exitAddress_value(Pract3Parser.Address_valueContext ctx);
}