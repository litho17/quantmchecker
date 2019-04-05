/*
 * Copyright 2006-2014 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.jrecruiter.hibernate;

import java.io.Serializable;
import java.util.Locale;

import org.hibernate.AssertionFailure;
import org.hibernate.cfg.DefaultNamingStrategy;
import org.hibernate.cfg.NamingStrategy;
import org.hibernate.internal.util.StringHelper;
import org.jvnet.inflector.Noun;
import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

/**
 * An improved naming strategy that prefers embedded
 * underscores to mixed case names
 * @see DefaultNamingStrategy the default strategy
 *
 * @author Gavin King
 * @author Gunnar Hillert
 */
public class ImprovedPluralizedNamingStrategy implements NamingStrategy, Serializable {

	/** serialVersionUID. */
	private static final long serialVersionUID = 0L;

	/**
	 * A convenient singleton instance
	 */
	public static final NamingStrategy INSTANCE = new ImprovedPluralizedNamingStrategy();

	/**
	 * Return the unqualified class name, mixed case converted to
	 * underscores
	 */
	public String classToTableName(String className) {
		return addUnderscores( StringHelper.unqualify(className), true );
	}
	/**
	 * Return the full property path with underscore seperators, mixed
	 * case converted to underscores
	 */
	public String propertyToColumnName(String propertyName) {
		return addUnderscores( StringHelper.unqualify(propertyName) );
	}
	/**
	 * Convert mixed case to underscores
	 */
	public String tableName(String tableName) {
		return addUnderscores(tableName);
	}
	/**
	 * Convert mixed case to underscores
	 */
	public String columnName(String columnName) {
		return addUnderscores(columnName);
	}

	protected static String addUnderscores(String name) {
		return addUnderscores(name, false);
	}

	protected static String addUnderscores(String name, boolean pluralize) {
		@Bound("+ name (* 2 splitTableNameFragments)") int k;
		@Inv("= (- buf i) (- c85 c87)") StringBuffer buf = new StringBuffer( name.replace('.', '_') );
		@Iter("<= i name") int i=1;
		for (; i<buf.length()-1;) {
			if (
				Character.isLowerCase( buf.charAt(i-1) ) &&
				Character.isUpperCase( buf.charAt(i) ) &&
				Character.isLowerCase( buf.charAt(i+1) )
			) {
				c85: buf.insert(i++, '_');
			}
			c87: i = i + 1;
		}

		if (pluralize) {
			String[] splitTableNameFragments = buf.toString().toLowerCase().split("_");

			@Inv("= (- buf2 j j) (- (+ c98 c99 c101) c105 c105)") StringBuffer buf2 = new StringBuffer();

			@Iter("<= j splitTableNameFragments") int j = 0;
			for (; j<splitTableNameFragments.length;) {

				if (j<(splitTableNameFragments.length-1)) {
					c98: buf2.append(splitTableNameFragments[j]);
					c99: buf2.append("_");
				} else {
					c101: buf2.append(
							Noun.pluralOf(
									splitTableNameFragments[j], Locale.ENGLISH));
				}
				c105: j = j + 1;
			}

			return buf2.toString().toUpperCase();
		}

		return buf.toString().toUpperCase();
	}

	public String collectionTableName(
			String ownerEntity, String ownerEntityTable, String associatedEntity, String associatedEntityTable,
			String propertyName
	) {
		return tableName( Noun.pluralOf(ownerEntityTable, Locale.ENGLISH) + '_' + propertyToColumnName(propertyName) );
	}

	/**
	 * Return the argument
	 */
	public String joinKeyColumnName(String joinedColumn, String joinedTable) {
		return columnName( joinedColumn );
	}

	/**
	 * Return the property name or propertyTableName
	 */
	public String foreignKeyColumnName(
			String propertyName, String propertyEntityName, String propertyTableName, String referencedColumnName
	) {
		String header = propertyName != null ? StringHelper.unqualify( propertyName ) : propertyTableName;
		if (header == null) {
			throw new AssertionFailure("NamingStrategy not properly filled");
		}
		return columnName( header ); //+ "_" + referencedColumnName not used for backward compatibility
	}

	/**
	 * Return the column name or the unqualified property name
	 */
	public String logicalColumnName(String columnName, String propertyName) {
		return StringHelper.isNotEmpty( columnName ) ? columnName : StringHelper.unqualify( propertyName );
	}

	/**
	 * Returns either the table name if explicit or
	 * if there is an associated table, the concatenation of owner entity table and associated table
	 * otherwise the concatenation of owner entity table and the unqualified property name
	 */
	public String logicalCollectionTableName(String tableName,
											String ownerEntityTable, String associatedEntityTable, String propertyName
	) {
		if ( tableName != null ) {
			return tableName;
		}
		else {
			//use of a stringbuffer to workaround a JDK bug
			return new StringBuffer(Noun.pluralOf(
					ownerEntityTable, Locale.ENGLISH)).append("_")
					.append(
						associatedEntityTable != null ?
								Noun.pluralOf(associatedEntityTable, Locale.ENGLISH) :
						StringHelper.unqualify( propertyName )
					).toString();
		}
	}
	/**
	 * Return the column name if explicit or the concatenation of the property name and the referenced column
	 */
	public String logicalCollectionColumnName(String columnName, String propertyName, String referencedColumn) {
		return StringHelper.isNotEmpty( columnName ) ?
				columnName :
				StringHelper.unqualify( propertyName ) + "_" + referencedColumn;
	}
}
