/*
 * Copyright (c) 2009-2016 Matthew R. Harrah
 *
 * MIT License
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */
package infotrader.src.infotrader.parser.parser;

import infotrader.src.infotrader.parser.model.Trailer;
import infotrader.src.infotrader.parser.model.Header;
import infotrader.src.infotrader.parser.model.StringTree;
import infotrader.src.infotrader.parser.model.Note;
import infotrader.src.infotrader.parser.model.Multimedia;
import infotrader.src.infotrader.parser.model.InfoTrader;
import infotrader.src.infotrader.parser.model.Source;
import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;

import infotrader.src.infotrader.parser.exception.InfoTraderParserException;
import infotrader.src.infotrader.parser.exception.ParserCancelledException;
import infotrader.src.infotrader.parser.io.event.FileProgressEvent;
import infotrader.src.infotrader.parser.io.event.FileProgressListener;
import infotrader.src.infotrader.parser.io.reader.InfoTraderFileReader;
import infotrader.src.infotrader.parser.parser.event.ParseProgressEvent;
import infotrader.src.infotrader.parser.parser.event.ParseProgressListener;
import java.io.File;

/**
 * <p>
 * Class for parsing GEDCOM 5.5 files and creating a { InfoTrader} structure from them.
 * </p>
 * <p>
 * General usage is as follows:
 * </p>
 * <ol>
 * <li>Instantiate a <code>GedcomParser</code> object</li>
 * <li>Call the <code>GedcomParser.load()</code> method (in one of its various forms) to parse a file/stream</li>
 * <li>Access the parser's <code>gedcom</code> property to access the parsed data</li>
 * </ol>
 * <p>
 * It is <b>highly recommended</b> that after calling the <code>GedcomParser.load()</code> method, the user check the
 * { GedcomParser#errors} and { GedcomParser#warnings} collections to see if anything problematic was
 * encountered in the data while parsing. Most commonly, the <code>warnings</code> collection will have information
 * about tags from GEDCOM 5.5.1 that were specified in a file that was designated as a GEDCOM 5.5 file. When this
 * occurs, the data is loaded, but will not be able to be written by { org.gedcom4j.writer.GedcomWriter} until the
 * version number in the <code>gedcomVersion</code> field of { Gedcom#header} is updated to
 * { SupportedVersion#V5_5_1}, or the 5.5.1-specific data is cleared from the data.
 * </p>
 * <p>
 * The parser takes a "forgiving" approach where it tries to load as much data as possible, including 5.5.1 data in a
 * file that says it's in 5.5 format, and vice-versa. However, when it finds inconsistencies, it will add messages to
 * the warnings and errors collections. Most of these messages indicate that the data was loaded, even though it was
 * incorrect, and the data will need to be corrected before it can be written.
 * </p>
 * 
 * <p>
 * The parser makes the assumption that if the version of GEDCOM used is explicitly specified in the file header, that
 * the rest of the data in the file should conform to that spec. For example, if the file header says the file is in 5.5
 * format (i.e., has a VERS 5.5 tag), then it will generate warnings if the new 5.5.1 tags (e.g., EMAIL) are encountered
 * elsewhere, but will load the data anyway. If no version is specified, the 5.5.1 format is assumed as a default.
 * </p>
 * 
 * <p>
 * This approach was selected based on the presumption that most of the uses of GEDCOM4J will be to read GEDCOM files
 * rather than to write them, so this provides that use case with the lowest friction.
 * </p>
 * 
 * @author frizbog1
 * 
 */
@SuppressWarnings("PMD.TooManyMethods")
public class InfoTraderParser extends AbstractParser<InfoTrader> {

    /**
     * The things that went wrong while parsing the gedcom file
     */
    private final List<String> errors = new ArrayList<String>();

    /**
     * The content of the gedcom file
     */
    public final InfoTrader infoTrader = new InfoTrader();

    /**
     * Indicates whether handling of custom tags should be strict - that is, must an unrecognized tag begin with an
     * underscore to be loaded into the custom tags collection? If false, unrecognized tags will be treated as custom
     * tags even if they don't begin with underscores, and no errors will be issued. If true, unrecognized tags that do
     * not begin with underscores will be discarded, with errors added to the errors collection.
     */
    private boolean strictCustomTags = true;

    /**
     * Indicates whether non-compliant GEDCOM files with actual line breaks in text values (rather than CONT tags)
     * should be parsed (with some loss of data) rather than fail with an exception.
     */
    private boolean strictLineBreaks = true;

    /**
     * The warnings issued during the parsing of the gedcom file
     */
    private final List<String> warnings = new ArrayList<String>();

    /**
     * Is the load/parse process being cancelled
     */
    private boolean cancelled;

    /**
     * Send a notification to listeners every time this many lines (or more) are read
     */
    private int readNotificationRate = 500;

    /**
     * The list of observers on file operations
     */
    private final List<WeakReference<FileProgressListener>> fileObservers = new CopyOnWriteArrayList<WeakReference<FileProgressListener>>();

    /**
     * The list of observers on parsing
     */
    private final List<WeakReference<ParseProgressListener>> parseObservers = new CopyOnWriteArrayList<WeakReference<ParseProgressListener>>();

    /**
     * Get a notification whenever this many items (or more) have been parsed
     */
    private int parseNotificationRate = 500;

    /**
     * The { StringTreeBuilder} that is assisting this class
     */
    private StringTreeBuilder stringTreeBuilder;

    /**
     * The 1-based line number that we've most recently read, so starts at zero (when we haven't read any lines yet)
     */
    private int lineNum;

    /**
     * Default constructor
     */
    public InfoTraderParser() {
        /*
         * This is the root level parser, so there are no parent or other root nodes to hook up to (yet)
         */
        super(null, null, null);
        InfoTraderParser = this;
    }

    /**
     * Indicate that file loading should be cancelled
     */
    public void cancel() {
        cancelled = true;
    }

    /**
     * Get the errors
     * 
     * @return the errors
     */
    public List<String> getErrors() {
        return errors;
    }

    /**
     * Get the fileObservers
     * 
     * @return the fileObservers
     */
    public List<WeakReference<FileProgressListener>> getFileObservers() {
        return fileObservers;
    }

    /**
     * Get the gedcom
     * 
     * @return the gedcom
     */
    public InfoTrader getInfoTrader() {
        return infoTrader;
    }

    /**
     * Get the parse notification rate (the number of items that get parsed between each notification, if listening)
     * 
     * @return the parse notification rate (the number of items that get parsed between each notification, if listening)
     */
    public int getParseNotificationRate() {
        return parseNotificationRate;
    }

    /**
     * Get the parseObservers
     * 
     * @return the parseObservers
     */
    public List<WeakReference<ParseProgressListener>> getParseObservers() {
        return parseObservers;
    }

    /**
     * Get the read notification rate
     * 
     * @return the read notification rate
     */
    public int getReadNotificationRate() {
        return readNotificationRate;
    }

    /**
     * Get the warnings
     * 
     * @return the warnings
     */
    public List<String> getWarnings() {
        return warnings;
    }

    /**
     * Is the load and parse operation cancelled?
     * 
     * @return whether the load and parse operation is cancelled
     */
    public boolean isCancelled() {
        return cancelled;
    }

    /**
     * Get the strictCustomTags
     * 
     * @return the strictCustomTags
     */
    public boolean isStrictCustomTags() {
        return strictCustomTags;
    }

    /**
     * Get the strictLineBreaks
     * 
     * @return the strictLineBreaks
     */
    public boolean isStrictLineBreaks() {
        return strictLineBreaks;
    }

    /**
     * Read data from an { java.io.InputStream} and construct a { StringTree} object from its contents
     * 
     * @param bytes
     *            the input stream over the bytes of the file
     * @throws IOException
     *             if there is a problem reading the data from the reader
     * @throws InfoTraderParserException
     *             if there is an error with parsing the data from the stream
     */
    public void load(BufferedInputStream bytes) throws IOException, InfoTraderParserException {
        // Reset counters and stuff
        lineNum = 0;
        errors.clear();
        warnings.clear();
        cancelled = false;

        if (cancelled) {
            throw new ParserCancelledException("File load/parse cancelled");
        }
        InfoTraderFileReader gfr = new InfoTraderFileReader(this, bytes);
        stringTreeBuilder = new StringTreeBuilder(this);
        String line = gfr.nextLine();
        while (line != null) {
            //System.out.println("line:"+line);
            if (line.charAt(0) == '0') {
                // We've hit the start of the next root node
                
                parseAndLoadPreviousStringTree();
            }

            lineNum++;
            stringTreeBuilder.appendLine(line);
            line = gfr.nextLine();
            if (cancelled) {
                throw new ParserCancelledException("File load/parse is cancelled");
            }
            if (lineNum % parseNotificationRate == 0) {
                notifyParseObservers(new ParseProgressEvent(this, infoTrader, false, lineNum));
            }

        }
        parseAndLoadPreviousStringTree();
    }

    /**
     * Load a gedcom file with the supplied name
     * 
     * @param filename
     *            the name of the file to load
     * @throws IOException
     *             if the file cannot be read
     * @throws InfoTraderParserException
     *             if the file cannot be parsed
     */
    public void load(File filename) throws IOException, InfoTraderParserException {
        FileInputStream fis = new FileInputStream(filename);
        BufferedInputStream bis = null;
        try {
            bis = new BufferedInputStream(fis);
            load(bis);
        } finally {
            if (bis != null) {
                bis.close();
            }
            fis.close();
        }
    }

    /**
     * Notify all listeners about the change
     * 
     * @param e
     *            the change event to tell the observers
     */
    public void notifyFileObservers(FileProgressEvent e) {
        int i = 0;
        while (i < fileObservers.size()) {
            WeakReference<FileProgressListener> observerRef = fileObservers.get(i);
            if (observerRef == null) {
                fileObservers.remove(observerRef);
            } else {
                FileProgressListener l = observerRef.get();
                if (l != null) {
                    l.progressNotification(e);
                }
                i++;
            }
        }
    }

    /**
     * Register a observer (listener) to be informed about progress and completion.
     * 
     * @param observer
     *            the observer you want notified
     */
    public void registerFileObserver(FileProgressListener observer) {
        fileObservers.add(new WeakReference<FileProgressListener>(observer));
    }

    /**
     * Register a observer (listener) to be informed about progress and completion.
     * 
     * @param observer
     *            the observer you want notified
     */
    public void registerParseObserver(ParseProgressListener observer) {
        parseObservers.add(new WeakReference<ParseProgressListener>(observer));
    }

    /**
     * Set the parse notification rate (the number of items that get parsed between each notification, if listening)
     * 
     * @param parseNotificationRate
     *            the parse notification rate (the number of items that get parsed between each notification, if
     *            listening). Must be at least 1.
     */
    public void setParseNotificationRate(int parseNotificationRate) {
        if (parseNotificationRate < 1) {
            throw new IllegalArgumentException("Parse Notification Rate must be at least 1");
        }
        this.parseNotificationRate = parseNotificationRate;
    }

    /**
     * Set the read notification rate.
     * 
     * @param readNotificationRate
     *            the read notification rate. Must be a positive integer.
     */
    public void setReadNotificationRate(int readNotificationRate) {
        if (readNotificationRate < 1) {
            throw new IllegalArgumentException("Read Notification Rate must be at least 1");
        }
        this.readNotificationRate = readNotificationRate;
    }

    /**
     * Set the strictCustomTags
     * 
     * @param strictCustomTags
     *            the strictCustomTags to set
     */
    public void setStrictCustomTags(boolean strictCustomTags) {
        this.strictCustomTags = strictCustomTags;
    }

    /**
     * Set the strictLineBreaks
     * 
     * @param strictLineBreaks
     *            the strictLineBreaks to set
     */
    public void setStrictLineBreaks(boolean strictLineBreaks) {
        this.strictLineBreaks = strictLineBreaks;
    }

    /**
     * Unregister a observer (listener) to be informed about progress and completion.
     * 
     * @param observer
     *            the observer you want notified
     */
    public void unregisterFileObserver(FileProgressListener observer) {
        int i = 0;
        while (i < fileObservers.size()) {
            WeakReference<FileProgressListener> observerRef = fileObservers.get(i);
            if (observerRef == null || observerRef.get() == observer) {
                fileObservers.remove(observerRef);
            } else {
                i++;
            }
        }
        fileObservers.add(new WeakReference<FileProgressListener>(observer));
    }

    /**
     * Unregister a observer (listener) to be informed about progress and completion.
     * 
     * @param observer
     *            the observer you want notified
     */
    public void unregisterParseObserver(ParseProgressListener observer) {
        int i = 0;
        while (i < parseObservers.size()) {
            WeakReference<ParseProgressListener> observerRef = parseObservers.get(i);
            if (observerRef == null || observerRef.get() == observer) {
                parseObservers.remove(observerRef);
            } else {
                i++;
            }
        }
        parseObservers.add(new WeakReference<ParseProgressListener>(observer));
    }

    /**
     * Get the line number we're reading
     * 
     * @return the line number we're reading
     */
    int getLineNum() {
        return lineNum;
    }

    /**
     * {@inheritDoc}
     * <p>
     * Note: Not implemented in this base { InfoTraderParser} class. Things in this class are handled by the
     * { #load(BufferedInputStream)} method.
     */
    @Override
    void parse() {
        // Do nothing
    }

    /**
     * Load a single root-level item
     * 
     * @param rootLevelItem
     *            the string tree for the root level item
     * @throws InfoTraderParserException
     *             if the data cannot be parsed because it's not in the format expected
     */
    private void loadRootItem(StringTree rootLevelItem) throws InfoTraderParserException {
        if (Tag.HEADER.equalsText(rootLevelItem.getTag())) {
            Header header = infoTrader.getHeader();
            if (header == null) {
                header = new Header();
                infoTrader.setHeader(header);
            }
            new HeaderParser(this, rootLevelItem, header).parse();
        }  else if (Tag.NOTE.equalsText(rootLevelItem.getTag())) {
            List<Note> dummyList = new ArrayList<Note>();
            new NoteListParser(this, rootLevelItem, dummyList).parse();
            if (!dummyList.isEmpty()) {
                throw new InfoTraderParserException("At root level NOTE structures should have @ID@'s");
            }
        }  else if (Tag.TRAILER.equalsText(rootLevelItem.getTag())) {
            infoTrader.setTrailer(new Trailer());
        } else if (Tag.SOURCE.equalsText(rootLevelItem.getTag())) {
            Source s = getSource(rootLevelItem.getId());
            new SourceParser(this, rootLevelItem, s).parse();
        } else if (Tag.OBJECT_MULTIMEDIA.equalsText(rootLevelItem.getTag())) {
            Multimedia multimedia = getMultimedia(rootLevelItem.getId());
            new MultimediaRecordParser(this, rootLevelItem, multimedia).parse();
        } else {
            unknownTag(rootLevelItem, infoTrader);
        }
    }

    /**
     * Notify all listeners about the change
     * 
     * @param e
     *            the change event to tell the observers
     */
    private void notifyParseObservers(ParseProgressEvent e) {
        int i = 0;
        while (i < parseObservers.size()) {
            WeakReference<ParseProgressListener> observerRef = parseObservers.get(i);
            if (observerRef == null) {
                parseObservers.remove(observerRef);
            } else {
                ParseProgressListener l = observerRef.get();
                if (l != null) {
                    l.progressNotification(e);
                }
                i++;
            }
        }
    }

    /**
     * Parse the { StringTreeBuilder}'s string tree in memory, load it into the object model, then discard that
     * string tree buffer
     * 
     * @throws InfoTraderParserException
     *             if the string tree contents cannot be parsed, or parsing was cancelled
     */
    private void parseAndLoadPreviousStringTree() throws InfoTraderParserException {
        //System.out.println("new tree");
        StringTree tree = stringTreeBuilder.getTree();
        if (tree != null && tree.getLevel() == -1 && tree.getChildren() != null && tree.getChildren().size() == 1) {
            // We've still got the prior root node in memory - parse it and add to object model
            StringTree rootLevelItem = stringTreeBuilder.getTree().getChildren().get(0);
            if (rootLevelItem.getLevel() != 0) {
                throw new InfoTraderParserException("Expected a root level item in the buffer, but found " + rootLevelItem.getLevel() + " " + rootLevelItem.getTag()
                        + " from line " + lineNum);
            }
            loadRootItem(rootLevelItem);
            // And discard it, now that it's loaded
            stringTreeBuilder = new StringTreeBuilder(this);
        }
    }

}
