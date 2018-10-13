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
package infotrader.src.infotrader.parser.io.reader;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

import infotrader.src.infotrader.parser.exception.InfoTraderParserException;
import infotrader.src.infotrader.parser.parser.InfoTraderParser;

/**
 * A reader that loads from an input stream and gives back a collection of strings representing the data therein. This
 * implementation handles UTF-8 data
 * 
 * @author frizbog
 */
final class Utf8Reader extends AbstractEncodingSpecificReader {

    /**
     * Was a byte order marker read when inspecting the file to detect encoding?
     */
    private boolean byteOrderMarkerRead = false;

    /**
     * Input stream reader for internal use over the byte stream
     */
    private final InputStreamReader inputStreamReader;

    /**
     * Buffered reader over the input stream reader, for internal use
     */
    private final BufferedReader bufferedReader;

    /**
     * The progress tracking input stream
     */
    private ProgressTrackingInputStream inputStream;

    /**
     * Constructor
     * 
     * @param parser
     *            the { InfoTraderParser} which is using this object to read files
     * 
     * @param byteStream
     *            the stream of data to read
     * @throws IOException
     *             if there's a problem reading the data
     */
    Utf8Reader(InfoTraderParser parser, InputStream byteStream) throws IOException {
        super(parser, byteStream);
        try {
            inputStream = new ProgressTrackingInputStream(byteStream);
            inputStreamReader = new InputStreamReader(inputStream, "UTF8");

            if (byteOrderMarkerRead) {
                // discard the byte order marker if one was detected
                inputStreamReader.read();
                bytesRead = inputStream.getBytesRead();
            }

            bufferedReader = new BufferedReader(inputStreamReader);
        } catch (IOException e) {
            closeReaders();
            throw e;
        }
    }

    @Override
    public String nextLine() throws IOException, InfoTraderParserException {
        String result = null;
        String s = bufferedReader.readLine();
        bytesRead = inputStream.getBytesRead();

        // Strip off Byte Order Mark if needed
        if (s != null && s.length() > 0 && s.charAt(0) == ((char) 0xFEFF)) {
            s = s.substring(1);
        }

        while (s != null)

        {
            if (s.length() != 0) {
                result = s;
                break;
            }
            s = bufferedReader.readLine();
            bytesRead = inputStream.getBytesRead();
        }
        bytesRead = inputStream.getBytesRead();
        return result;
    }

    /**
     * Set whether or not a byte order marker was read when inspecting the file to detect its encoding
     * 
     * @param wasByteOrderMarkerRead
     *            true if a byte order marker was read
     */
    public void setByteOrderMarkerRead(boolean wasByteOrderMarkerRead) {
        byteOrderMarkerRead = wasByteOrderMarkerRead;
    }

    @Override
    void cleanUp() throws IOException {
        closeReaders();
    }

    /**
     * Close the readers created in this class. Private so it can't be overridden (like { #cleanUp()} can be),
     * which makes it safe to call from the constructor.
     * 
     * @throws IOException
     *             if the readers can't be closed
     */
    private void closeReaders() throws IOException {
        if (bufferedReader != null) {
            bufferedReader.close();
        }
        if (inputStreamReader != null) {
            inputStreamReader.close();
        }
    }

}
