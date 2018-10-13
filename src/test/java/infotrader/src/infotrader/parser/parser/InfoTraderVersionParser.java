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

import infotrader.src.infotrader.parser.exception.UnsupportedVersionException;
import infotrader.src.infotrader.parser.model.InfoTraderVersion;
import infotrader.src.infotrader.parser.model.StringTree;
import infotrader.src.infotrader.parser.model.StringWithCustomTags;
import infotrader.src.infotrader.parser.model.SupportedVersion;

/**
 * A parser for { InfoTraderVersion} objects.
 * 
 * @author frizbog
 */
class InfoTraderVersionParser extends AbstractParser<InfoTraderVersion> {

    /**
     * Constructor
     * 
     * @param gedcomParser
     *            a reference to the root { InfoTraderParser}
     * @param stringTree
     *            { StringTree} to be parsed
     * @param loadInto
     *            the object we are loading data into
     */
    InfoTraderVersionParser(InfoTraderParser gedcomParser, StringTree stringTree, InfoTraderVersion loadInto) {
        super(gedcomParser, stringTree, loadInto);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    void parse() {
        if (stringTree.getChildren() != null) {
            for (StringTree ch : stringTree.getChildren()) {
                if (Tag.VERSION.equalsText(ch.getTag())) {
                    SupportedVersion vn = null;
                    try {
                        vn = SupportedVersion.forString(ch.getValue());
                    } catch (UnsupportedVersionException e) {
                        addError(e.getMessage());
                    }
                    loadInto.setVersionNumber(vn);
                } else if (Tag.FORM.equalsText(ch.getTag())) {
                    loadInto.setInfoTraderForm(new StringWithCustomTags(ch));
                } else {
                    unknownTag(ch, loadInto);
                }
            }
        }
    }

}
