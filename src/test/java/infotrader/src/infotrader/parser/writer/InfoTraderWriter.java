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
package infotrader.src.infotrader.parser.writer;

import infotrader.src.infotrader.parser.model.Corporation;
import infotrader.src.infotrader.parser.model.SupportedVersion;
import infotrader.src.infotrader.parser.model.StringWithCustomTags;
import infotrader.src.infotrader.parser.model.InfoTraderVersion;
import infotrader.src.infotrader.parser.model.StringTree;
import infotrader.src.infotrader.parser.model.Multimedia;
import infotrader.src.infotrader.parser.model.InfoTrader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.lang.ref.WeakReference;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;

import infotrader.src.infotrader.parser.exception.InfoTraderWriterException;
import infotrader.src.infotrader.parser.exception.InfoTraderWriterVersionDataMismatchException;
import infotrader.src.infotrader.parser.exception.WriterCancelledException;
import infotrader.src.infotrader.parser.io.event.FileProgressEvent;
import infotrader.src.infotrader.parser.io.event.FileProgressListener;
import infotrader.src.infotrader.parser.io.writer.InfoTraderFileWriter;
import infotrader.src.infotrader.parser.validate.InfoTraderValidationFinding;
import infotrader.src.infotrader.parser.validate.InfoTraderValidator;
import infotrader.src.infotrader.parser.validate.Severity;
import infotrader.src.infotrader.parser.writer.event.ConstructProgressEvent;
import infotrader.src.infotrader.parser.writer.event.ConstructProgressListener;

/**
 * <p>
 * A class for writing the gedcom structure out as a GEDCOM 5.5 compliant file.
 * </p>
 * <p>
 * General usage is as follows:
 * </p>
 * <ul>
 * <li>Instantiate a <code>GedcomWriter</code>, passing the { InfoTrader} to be written as a parameter to the
 * constructor.</li>
 * <li>Call one of the variants of the <code>write</code> method to write the data</li>
 * <li>Optionally check the contents of the { #validationFindings} collection to see if there was anything
 * problematic found in your data.</li>
 * </ul>
 * 
 * <h3>Validation</h3>
 * <p>
 * By default, this class automatically validates your data prior to writing it by using a
 * { infotrader.src.infotrader.parser.validate.InfoTraderValidator}. This is to prevent writing data that does not conform to the spec.
 * </p>
 * 
 * <p>
 * If validation finds any errors that are of severity ERROR, the writer will throw an Exception (usually
 * { InfoTraderWriterVersionDataMismatchException} or { InfoTraderWriterException}). If this occurs, check the
 * { #validationFindings} collection to determine what the problem was.
 * </p>
 * 
 * <p>
 * Although validation is automatically performed, autorepair is turned off by default (see
 * { org.gedcom4j.validate.GedcomValidator#setAutorepairEnabled(boolean)})...this way your data is not altered.
 * Validation can be suppressed if you want by setting { #validationSuppressed} to true, but this is not
 * recommended. You can also force autorepair on if you want.
 * </p>
 * 
 * @author frizbog1
 */
public class InfoTraderWriter extends AbstractEmitter<InfoTrader> {
    /**
     * The text lines of the GEDCOM file we're writing, which will be written using a { InfoTraderFileWriter}.
     * Deliberately package-private so tests can access it but others can't alter it.
     */
    List<String> lines = new ArrayList<String>();

    /**
     * Are we suppressing the call to the validator? Deliberately package-private so unit tests can fiddle with it to
     * make testing easy.
     */
    boolean validationSuppressed = true;

    /**
     * Whether or not to use autorepair in the validation step
     */
    private boolean autorepair = false;

    /**
     * Has this writer been cancelled?
     */
    private boolean cancelled;

    /**
     * Send a notification whenever more than this many lines are constructed
     */
    private int constructionNotificationRate = 500;

    /**
     * The list of observers on string construction
     */
    private final List<WeakReference<ConstructProgressListener>> constructObservers = new CopyOnWriteArrayList<WeakReference<ConstructProgressListener>>();

    /**
     * Send a notification whenever more than this many lines are written to a file
     */
    private int fileNotificationRate = 500;

    /**
     * The list of observers on file operations
     */
    private final List<WeakReference<FileProgressListener>> fileObservers = new CopyOnWriteArrayList<WeakReference<FileProgressListener>>();

    /**
     * The number of lines constructed as last reported to the observers
     */
    private int lastLineCountNotified = 0;

    /**
     * Whether to use little-endian unicode
     */
    private boolean useLittleEndianForUnicode = true;

    /**
     * A list of things found during validation of the gedcom data prior to writing it. If the data cannot be written
     * due to an exception caused by failure to validate, this collection will describe the issues encountered.
     */
    private List<InfoTraderValidationFinding> validationFindings;

    /**
     * Constructor
     * 
     * @param gedcom
     *            the { InfoTrader} structure to write out
     * @throws WriterCancelledException
     *             if cancellation was requested during the operation
     */
    public InfoTraderWriter(InfoTrader gedcom) throws WriterCancelledException {
        super(null, 0, gedcom);
        baseWriter = this;
    }

    /**
     * Cancel construction of the GEDCOM and writing it to a file
     */
    public void cancel() {
        cancelled = true;
    }

    /**
     * Get the construction notification rate - how many lines need to be constructed before getting a notification
     * 
     * @return the construction notification rate - how many lines need to be constructed before getting a notification
     */
    public int getConstructionNotificationRate() {
        return constructionNotificationRate;
    }

    /**
     * Get the number of lines to be written between each file notification
     * 
     * @return the number of lines to be written between each file notification
     */
    public int getFileNotificationRate() {
        return fileNotificationRate;
    }

    /**
     * Get the validationFindings
     * 
     * @return the validationFindings
     */
    public List<InfoTraderValidationFinding> getValidationFindings() {
        return validationFindings;
    }

    /**
     * Get the autorepair
     * 
     * @return the autorepair
     */
    public boolean isAutorepair() {
        return autorepair;
    }

    /**
     * Has this writer been cancelled?
     * 
     * @return true if this writer has been cancelled
     */
    public boolean isCancelled() {
        return cancelled;
    }

    /**
     * Get the useLittleEndianForUnicode
     * 
     * @return the useLittleEndianForUnicode
     */
    public boolean isUseLittleEndianForUnicode() {
        return useLittleEndianForUnicode;
    }

    /**
     * Notify all listeners about the file progress
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
    public void registerConstructObserver(ConstructProgressListener observer) {
        constructObservers.add(new WeakReference<ConstructProgressListener>(observer));
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
     * Set the autorepair
     * 
     * @param autorepair
     *            the autorepair to set
     */
    public void setAutorepair(boolean autorepair) {
        this.autorepair = autorepair;
    }

    /**
     * Set the construction notification rate - how many lines need to be constructed before getting a notification
     * 
     * @param constructionNotificationRate
     *            the construction notification rate - how many lines need to be constructed before getting a
     *            notification. Must be 1 or greater.
     */
    public void setConstructionNotificationRate(int constructionNotificationRate) {
        if (constructionNotificationRate < 1) {
            throw new IllegalArgumentException("Construction Notification Rate must be at least 1");
        }
        this.constructionNotificationRate = constructionNotificationRate;
    }

    /**
     * Set the number of lines to be written between each file notification
     * 
     * @param fileNotificationRate
     *            the number of lines to be written between each file notification. Must be 1 or greater.
     */
    public void setFileNotificationRate(int fileNotificationRate) {
        if (fileNotificationRate < 1) {
            throw new IllegalArgumentException("File Notification Rate must be at least 1");
        }
        this.fileNotificationRate = fileNotificationRate;
    }

    /**
     * Set the useLittleEndianForUnicode
     * 
     * @param useLittleEndianForUnicode
     *            the useLittleEndianForUnicode to set
     */
    public void setUseLittleEndianForUnicode(boolean useLittleEndianForUnicode) {
        this.useLittleEndianForUnicode = useLittleEndianForUnicode;
    }

    /**
     * Unregister a observer (listener) to be informed about progress and completion.
     * 
     * @param observer
     *            the observer you want notified
     */
    public void unregisterConstructObserver(ConstructProgressListener observer) {
        int i = 0;
        while (i < constructObservers.size()) {
            WeakReference<ConstructProgressListener> observerRef = constructObservers.get(i);
            if (observerRef == null || observerRef.get() == observer) {
                constructObservers.remove(observerRef);
            } else {
                i++;
            }
        }
        constructObservers.add(new WeakReference<ConstructProgressListener>(observer));
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
     * Write the { InfoTrader} data as a GEDCOM 5.5 file. Automatically fills in the value for the FILE tag in the HEAD
     * structure.
     * 
     * @param file
     *            the { File} to write to
     * @throws IOException
     *             if there's a problem writing the data
     * @throws InfoTraderWriterException
     *             if the data is malformed and cannot be written
     */
    public void write(File file) throws IOException, InfoTraderWriterException {
        // Automatically replace the contents of the filename in the header
        writeFrom.getHeader().setFileName(new StringWithCustomTags(file.getName()));

        // If the file doesn't exist yet, we have to create it, otherwise a FileNotFoundException will be thrown
        if (!file.exists() && !file.getCanonicalFile().getParentFile().exists() && !file.getCanonicalFile().getParentFile().mkdirs() && !file.createNewFile()) {
            throw new IOException("Unable to create file " + file.getName());
        }
        OutputStream o = new FileOutputStream(file);
        try {
            write(o);
            o.flush();
        } finally {
            o.close();
        }
    }

    /**
     * Write the { InfoTrader} data in GEDCOM 5.5 format to an output stream
     * 
     * @param out
     *            the output stream we're writing to
     * @throws InfoTraderWriterException
     *             if the data is malformed and cannot be written; or if the data fails validation with one or more
     *             finding of severity ERROR (and validation is not suppressed - see
     *             { GedcomWriter#validationSuppressed})
     */
    public void write(OutputStream out) throws InfoTraderWriterException {
        emit();
        try {
            InfoTraderFileWriter gfw = new InfoTraderFileWriter(this, lines);
            gfw.setUseLittleEndianForUnicode(useLittleEndianForUnicode);
            gfw.write(out);
        } catch (IOException e) {
            throw new InfoTraderWriterException("Unable to write file", e);
        }
    }

    /**
     * Write the { InfoTrader} data as a GEDCOM 5.5 file, with the supplied file name
     * 
     * @param filename
     *            the name of the file to write
     * @throws IOException
     *             if there's a problem writing the data
     * @throws InfoTraderWriterException
     *             if the data is malformed and cannot be written
     */
    public void write(String filename) throws IOException, InfoTraderWriterException {
        File f = new File(filename);
        write(f);
    }

    @Override
    protected void emit() throws InfoTraderWriterException {
        if (!validationSuppressed) {
            InfoTraderValidator gv = new InfoTraderValidator(writeFrom);
            gv.setAutorepairEnabled(autorepair);
            gv.validate();
            validationFindings = gv.getFindings();
            int numErrorFindings = 0;
            for (InfoTraderValidationFinding f : validationFindings) {
                if (f.getSeverity() == Severity.ERROR) {
                    numErrorFindings++;
                }
            }
            if (numErrorFindings > 0) {
                throw new InfoTraderWriterException("Cannot write file - " + numErrorFindings
                        + " error(s) found during validation.  Review the validation findings to determine root cause.");
            }
        }
        checkVersionCompatibility();
        new HeaderEmitter(baseWriter, 0, writeFrom.getHeader()).emit();
        new SubmissionEmitter(baseWriter, 0, writeFrom.getSubmission()).emit();
        
        if (g55()) {
            new Multimedia55Emitter(baseWriter, 0, writeFrom.getMultimedia().values()).emit();
        } else {
            new Multimedia551Emitter(baseWriter, 0, writeFrom.getMultimedia().values()).emit();
        }
        new NotesEmitter(baseWriter, 0, writeFrom.getNotes().values()).emit();
        new RepositoryEmitter(baseWriter, 0, writeFrom.getRepositories().values()).emit();
        new SourceEmitter(baseWriter, 0, writeFrom.getSources().values()).emit();
        new SubmittersEmitter(this, 0, writeFrom.getSubmitters().values()).emit();
        emitTrailer();
        emitCustomTags(1, writeFrom.getCustomTags());
    }

    /**
     * Emit the custom tags
     * 
     * @param customTags
     *            the custom tags
     * @param level
     *            the level at which the custom tags are to be written
     */
    @Override
    void emitCustomTags(int level, List<StringTree> customTags) {
        if (customTags != null) {
            for (StringTree st : customTags) {
                StringBuilder line = new StringBuilder(Integer.toString(level));
                line.append(" ");
                if (st.getId() != null && st.getId().trim().length() > 0) {
                    line.append(st.getId()).append(" ");
                }
                line.append(st.getTag());
                if (st.getValue() != null && st.getValue().trim().length() > 0) {
                    line.append(" ").append(st.getValue());
                }
                baseWriter.lines.add(line.toString());
                emitCustomTags(level + 1, st.getChildren());
            }
        }
    }

    /**
     * Notify construct observers if more than 100 lines have been constructed since last time we notified them
     */
    void notifyConstructObserversIfNeeded() {
        if ((lines.size() - lastLineCountNotified) > constructionNotificationRate) {
            notifyConstructObservers(new ConstructProgressEvent(this, lines.size(), true));
        }
    }

    /**
     * Checks that the gedcom version specified is compatible with the data in the model. Not a perfect exhaustive
     * check.
     * 
     * @throws InfoTraderWriterException
     *             if data is detected that is incompatible with the selected version
     */
    private void checkVersionCompatibility() throws InfoTraderWriterException {

        if (writeFrom.getHeader().getInfoTraderVersion() == null) {
            // If there's not one specified, set up a default one that specifies
            // 5.5.1
            writeFrom.getHeader().setInfoTraderVersion(new InfoTraderVersion());
        }
        if (SupportedVersion.V5_5.equals(writeFrom.getHeader().getInfoTraderVersion().getVersionNumber())) {
            checkVersionCompatibility55();
        } else {
            checkVersionCompatibility551();
        }

    }

    /**
     * Check that the data is compatible with 5.5 style Gedcom files
     * 
     * @throws InfoTraderWriterVersionDataMismatchException
     *             if a data point is detected that is incompatible with the 5.5 standard
     */
    private void checkVersionCompatibility55() throws InfoTraderWriterVersionDataMismatchException {
        // Now that we know if we're working with a 5.5.1 file or not, let's
        // check some data points
        if (writeFrom.getHeader().getCopyrightData() != null && writeFrom.getHeader().getCopyrightData().size() > 1) {
            throw new InfoTraderWriterVersionDataMismatchException("InfoTrader version is 5.5, but has multi-line copyright data in header");
        }
        if (writeFrom.getHeader().getCharacterSet() != null && writeFrom.getHeader().getCharacterSet().getCharacterSetName() != null && "UTF-8".equals(writeFrom
                .getHeader().getCharacterSet().getCharacterSetName().getValue())) {
            throw new InfoTraderWriterVersionDataMismatchException("InfoTrader version is 5.5, but data is encoded using UTF-8");
        }
        if (writeFrom.getHeader().getSourceSystem() != null && writeFrom.getHeader().getSourceSystem().getCorporation() != null) {
            Corporation c = writeFrom.getHeader().getSourceSystem().getCorporation();
            if (c.getWwwUrls() != null && !c.getWwwUrls().isEmpty()) {
                throw new InfoTraderWriterVersionDataMismatchException("InfoTrader version is 5.5, but source system corporation has www urls");
            }
            if (c.getFaxNumbers() != null && !c.getFaxNumbers().isEmpty()) {
                throw new InfoTraderWriterVersionDataMismatchException("InfoTrader version is 5.5, but source system corporation has fax numbers");
            }
            if (c.getEmails() != null && !c.getEmails().isEmpty()) {
                throw new InfoTraderWriterVersionDataMismatchException("InfoTrader version is 5.5, but source system corporation has emails");
            }
        }
    }

    /**
     * Check that the data is compatible with 5.5.1 style Gedcom files
     * 
     * @throws InfoTraderWriterVersionDataMismatchException
     *             if a data point is detected that is incompatible with the 5.5.1 standard
     * 
     */
    private void checkVersionCompatibility551() throws InfoTraderWriterVersionDataMismatchException {
        for (Multimedia m : writeFrom.getMultimedia().values()) {
            if (m.getBlob() != null && !m.getBlob().isEmpty()) {
                throw new InfoTraderWriterVersionDataMismatchException("InfoTrader version is 5.5.1, but multimedia item " + m.getXref()
                        + " contains BLOB data which is unsupported in 5.5.1");
            }
        }
    }

    /**
     * Write out the trailer record
     */
    private void emitTrailer() {
        lines.add("0 TRLR");
        notifyConstructObservers(new ConstructProgressEvent(this, lines.size(), true));
    }

    /**
     * Notify all listeners about the line being
     * 
     * @param e
     *            the change event to tell the observers
     */
    private void notifyConstructObservers(ConstructProgressEvent e) {
        int i = 0;
        lastLineCountNotified = e.getLinesProcessed();
        while (i < constructObservers.size()) {
            WeakReference<ConstructProgressListener> observerRef = constructObservers.get(i);
            if (observerRef == null) {
                constructObservers.remove(observerRef);
            } else {
                ConstructProgressListener l = observerRef.get();
                if (l != null) {
                    l.progressNotification(e);
                }
                i++;
            }
        }
    }
}
