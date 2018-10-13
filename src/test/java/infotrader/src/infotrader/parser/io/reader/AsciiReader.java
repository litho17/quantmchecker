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

import java.io.IOException;
import java.io.InputStream;

import infotrader.src.infotrader.parser.exception.InfoTraderParserException;
import infotrader.src.infotrader.parser.parser.InfoTraderParser;

/**
 * A reader that reads a single line from an Ascii-encoded file.
 * 
 * @author frizbog
 */
final class AsciiReader extends AbstractEncodingSpecificReader {

    /**
     * Are we at the end of file yet?
     */
    private boolean eof = false;

    /**
     * The line buffer for the current line
     */
    private final StringBuilder lineBuffer = new StringBuilder();

    /**
     * Constructor
     * 
     * @param parser
     *            the { InfoTraderParser} which is using this object to read files
     * 
     * @param byteStream
     *            stream of data to read
     */
    protected AsciiReader(InfoTraderParser parser, InputStream byteStream) {
        super(parser, byteStream);
    }

    @Override
    public String nextLine() throws IOException, InfoTraderParserException {
        String result = null;
        while (!eof) {
            int currChar = byteStream.read();
            if (currChar >= 0) {
                bytesRead++;
            }

            // Check for EOF
            if (currChar < 0) {
                // hit EOF - add final line buffer (last line) and get out
                eof = true;
                if (lineBuffer.length() > 0) {
                    result = lineBuffer.toString();
                }
                break;
            }

            // Ignore leading spaces
            if (currChar == ' ' && lineBuffer.length() == 0) {
                continue;
            }

            // Check for carriage returns or line feeds - signify EOL
            if ((currChar == 0x0D || currChar == 0x0A) && lineBuffer.length() > 0) {
                result = lineBuffer.toString();
                lineBuffer.setLength(0);
                break;
            }

            // All other characters in 0x00 to 0x7F range are treated the
            // same,
            // regardless of encoding, and added as is
            if (currChar < 0x80) {
                lineBuffer.append(Character.valueOf((char) currChar));
                continue;
            }

            // If we fell through to here, we have an extended character
            throw new IOException("Extended characters not supported in ASCII: 0x" + Integer.toHexString(currChar));
        }
        return result;
    }

    @Override
    void cleanUp() throws IOException {
        // do nothing
    }

}
