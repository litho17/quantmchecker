/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package tomcat.org.apache.tomcat.dbcp.dbcp2;

import java.sql.Connection;
import java.sql.PreparedStatement;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.Arrays;

import tomcat.org.apache.tomcat.dbcp.dbcp2.PoolingConnection.StatementType;

/**
 * A key uniquely identifying {@link java.sql.PreparedStatement PreparedStatement}s.
 * @since 2.0
 */
public class PStmtKey {

    /** SQL defining Prepared or Callable Statement */
    private final String _sql;

    /** Result set type */
    private final Integer _resultSetType;

    /** Result set concurrency */
    private final Integer _resultSetConcurrency;

    /** Result set holdability */
    private final Integer _resultSetHoldability;

    /** Database catalog */
    private final String _catalog;

    /** Auto generated keys */
    private final Integer _autoGeneratedKeys;

    /** column indexes */
    private final int[] _columnIndexes;

    /** column names */
    private final String[] _columnNames;

    /** Statement type */
    private final StatementType _stmtType;

    /** Statement builder */
    private StatementBuilder builder;

    public PStmtKey(final String sql) {
        this(sql, null, StatementType.PREPARED_STATEMENT);
    }

    public PStmtKey(final String sql, final String catalog) {
        this(sql, catalog, StatementType.PREPARED_STATEMENT);
    }

    public PStmtKey(final String sql, final String catalog, final StatementType stmtType) {
        _sql = sql;
        _catalog = catalog;
        _stmtType = stmtType;
        _autoGeneratedKeys = null;
        _columnIndexes = null;
        _columnNames = null;
        _resultSetType = null;
        _resultSetConcurrency = null;
        _resultSetHoldability = null;
        // create builder
        if (stmtType == StatementType.PREPARED_STATEMENT) {
            builder = new PreparedStatementSQL();
        } else if (stmtType == StatementType.CALLABLE_STATEMENT) {
            builder = new PreparedCallSQL();
        }
    }

    public PStmtKey(final String sql, final String catalog, final int autoGeneratedKeys) {
        this(sql, catalog, StatementType.PREPARED_STATEMENT, Integer.valueOf(autoGeneratedKeys));
    }

    public PStmtKey(final String sql, final String catalog, final StatementType stmtType, final Integer autoGeneratedKeys) {
        _sql = sql;
        _catalog = catalog;
        _stmtType = stmtType;
        _autoGeneratedKeys = autoGeneratedKeys;
        _columnIndexes = null;
        _columnNames = null;
        _resultSetType = null;
        _resultSetConcurrency = null;
        _resultSetHoldability = null;
        // create builder
        if (stmtType == StatementType.PREPARED_STATEMENT) {
            builder = new PreparedStatementWithAutoGeneratedKeys();
        } else if (stmtType == StatementType.CALLABLE_STATEMENT) {
            builder = new PreparedCallSQL();
        }
    }

    public PStmtKey(final String sql, final String catalog, final int[] columnIndexes) {
        _sql = sql;
        _catalog = catalog;
        _stmtType = StatementType.PREPARED_STATEMENT;
        _autoGeneratedKeys = null;
        _columnIndexes = columnIndexes;
        _columnNames = null;
        _resultSetType = null;
        _resultSetConcurrency = null;
        _resultSetHoldability = null;
        // create builder
        builder = new PreparedStatementWithColumnIndexes();
    }

    public PStmtKey(final String sql, final String catalog, final String[] columnNames) {
        _sql = sql;
        _catalog = catalog;
        _stmtType = StatementType.PREPARED_STATEMENT;
        _autoGeneratedKeys = null;
        _columnIndexes = null;
        _columnNames = columnNames;
        _resultSetType = null;
        _resultSetConcurrency = null;
        _resultSetHoldability = null;
        // create builder
        builder = new PreparedStatementWithColumnNames();
    }

    public  PStmtKey(final String sql, final int resultSetType, final int resultSetConcurrency) {
        this(sql, null, resultSetType, resultSetConcurrency, StatementType.PREPARED_STATEMENT);
    }

    public PStmtKey(final String sql, final String catalog, final int resultSetType, final int resultSetConcurrency) {
        this(sql, catalog, resultSetType, resultSetConcurrency, StatementType.PREPARED_STATEMENT);
    }

    public PStmtKey(final String sql, final String catalog, final int resultSetType, final int resultSetConcurrency, final StatementType stmtType) {
        _sql = sql;
        _catalog = catalog;
        _resultSetType = Integer.valueOf(resultSetType);
        _resultSetConcurrency = Integer.valueOf(resultSetConcurrency);
        _resultSetHoldability = null;
        _stmtType = stmtType;
        _autoGeneratedKeys = null;
        _columnIndexes = null;
        _columnNames = null;
        // create builder
        if (stmtType == StatementType.PREPARED_STATEMENT) {
            builder = new PreparedStatementWithResultSetConcurrency();
        } else if (stmtType == StatementType.CALLABLE_STATEMENT) {
            builder = new PreparedCallWithResultSetConcurrency();
        }
    }

    public PStmtKey(final String sql, final String catalog, final int resultSetType, final int resultSetConcurrency,
            final int resultSetHoldability) {
        this(sql, catalog, resultSetType, resultSetConcurrency, resultSetHoldability, StatementType.PREPARED_STATEMENT);
    }

    public PStmtKey(final String sql, final String catalog, final int resultSetType, final int resultSetConcurrency,
            final int resultSetHoldability, final StatementType stmtType) {
        _sql = sql;
        _catalog = catalog;
        _resultSetType = Integer.valueOf(resultSetType);
        _resultSetConcurrency = Integer.valueOf(resultSetConcurrency);
        _resultSetHoldability = Integer.valueOf(resultSetHoldability);
        _stmtType = stmtType;
        _autoGeneratedKeys = null;
        _columnIndexes = null;
        _columnNames = null;
        // create builder
        if (stmtType == StatementType.PREPARED_STATEMENT) {
            builder = new PreparedStatementWithResultSetHoldability();
        } else if (stmtType == StatementType.CALLABLE_STATEMENT) {
            builder = new PreparedCallWithResultSetHoldability();
        }
    }


    public String getSql() {
        return _sql;
    }

    public Integer getResultSetType() {
        return _resultSetType;
    }

    public Integer getResultSetConcurrency() {
        return _resultSetConcurrency;
    }

    public Integer getResultSetHoldability() {
        return _resultSetHoldability;
    }

    public Integer getAutoGeneratedKeys() {
        return _autoGeneratedKeys;
    }

    public int[] getColumnIndexes() {
        return _columnIndexes;
    }

    public String[] getColumnNames() {
        return _columnNames;
    }

    public String getCatalog() {
        return _catalog;
    }

    public StatementType getStmtType() {
        return _stmtType;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final PStmtKey other = (PStmtKey) obj;
        if (_catalog == null) {
            if (other._catalog != null) {
                return false;
            }
        } else if (!_catalog.equals(other._catalog)) {
            return false;
        }
        if (_resultSetConcurrency == null) {
            if (other._resultSetConcurrency != null) {
                return false;
            }
        } else if (!_resultSetConcurrency.equals(other._resultSetConcurrency)) {
            return false;
        }
        if (_resultSetType == null) {
            if (other._resultSetType != null) {
                return false;
            }
        } else if (!_resultSetType.equals(other._resultSetType)) {
            return false;
        }
        if (_resultSetHoldability == null) {
            if (other._resultSetHoldability != null) {
                return false;
            }
        } else if (!_resultSetHoldability.equals(other._resultSetHoldability)) {
            return false;
        }
        if (_autoGeneratedKeys == null) {
            if (other._autoGeneratedKeys != null) {
                return false;
            }
        } else if (!_autoGeneratedKeys.equals(other._autoGeneratedKeys)) {
            return false;
        }
        if (!Arrays.equals(_columnIndexes, other._columnIndexes)) {
            return false;
        }
        if (!Arrays.equals(_columnNames, other._columnNames)) {
            return false;
        }
        if (_sql == null) {
            if (other._sql != null) {
                return false;
            }
        } else if (!_sql.equals(other._sql)) {
            return false;
        }
        if (_stmtType != other._stmtType) {
            return false;
        }
        return true;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (_catalog == null ? 0 : _catalog.hashCode());
        result = prime * result + (_resultSetConcurrency == null ? 0 : _resultSetConcurrency.hashCode());
        result = prime * result + (_resultSetType == null ? 0 : _resultSetType.hashCode());
        result = prime * result + (_resultSetHoldability == null ? 0 : _resultSetHoldability.hashCode());
        result = prime * result + (_sql == null ? 0 : _sql.hashCode());
        result = prime * result + (_autoGeneratedKeys == null ? 0 : _autoGeneratedKeys.hashCode());
        result = prime * result + Arrays.hashCode(_columnIndexes);
        result = prime * result + Arrays.hashCode(_columnNames);
        result = prime * result + _stmtType.hashCode();
        return result;
    }

    @Override
    public String toString() {
        final StringBuffer buf = new StringBuffer();
        buf.append("PStmtKey: sql=");
        buf.append(_sql);
        buf.append(", catalog=");
        buf.append(_catalog);
        buf.append(", resultSetType=");
        buf.append(_resultSetType);
        buf.append(", resultSetConcurrency=");
        buf.append(_resultSetConcurrency);
        buf.append(", resultSetHoldability=");
        buf.append(_resultSetHoldability);
        buf.append(", autoGeneratedKeys=");
        buf.append(_autoGeneratedKeys);
        buf.append(", columnIndexes=");
        buf.append(Arrays.toString(_columnIndexes));
        buf.append(", columnNames=");
        buf.append(Arrays.toString(_columnNames));
        buf.append(", statementType=");
        buf.append(_stmtType);
        return buf.toString();
    }

    public Statement createStatement(final Connection connection) throws SQLException {
        if (builder == null) {
            throw new IllegalStateException("Prepared statement key is invalid.");
        }
        return builder.createStatement(connection);
    }

    /**
     * Interface for Prepared or Callable Statement
     */
    private interface StatementBuilder {
        public Statement createStatement(Connection connection) throws SQLException;
    }

    /**
     * Builder for prepareStatement(String sql)
     */
    private class PreparedStatementSQL implements StatementBuilder {
        @Override
        public Statement createStatement(final Connection connection) throws SQLException {
            final PreparedStatement statement = connection.prepareStatement(_sql);
            return statement;
        }
    }

    /**
     * Builder for prepareStatement(String sql, int autoGeneratedKeys)
     */
    private class PreparedStatementWithAutoGeneratedKeys implements StatementBuilder {
        @Override
        public Statement createStatement(final Connection connection) throws SQLException {
            final PreparedStatement statement = connection.prepareStatement(
                    _sql, _autoGeneratedKeys.intValue());
            return statement;
        }
    }

    /**
     * Builder for prepareStatement(String sql, int[] columnIndexes)
     */
    private class PreparedStatementWithColumnIndexes implements StatementBuilder {
        @Override
        public Statement createStatement(final Connection connection) throws SQLException {
            final PreparedStatement statement = connection.prepareStatement(
                    _sql, _columnIndexes);
            return statement;
        }
    }

    /**
     * Builder for prepareStatement(String sql, int resultSetType, int resultSetConcurrency)
     */
    private class PreparedStatementWithResultSetConcurrency implements StatementBuilder {
        @Override
        public Statement createStatement(final Connection connection) throws SQLException {
            final PreparedStatement statement = connection.prepareStatement(
                    _sql, _resultSetType.intValue(), _resultSetConcurrency.intValue());
            return statement;
        }
    }

    /**
     * Builder for prepareStatement(String sql, int resultSetType, int resultSetConcurrency, int resultSetHoldability)
     */
    private class PreparedStatementWithResultSetHoldability implements StatementBuilder {
        @Override
        public Statement createStatement(final Connection connection) throws SQLException {
            final PreparedStatement statement = connection.prepareStatement(
                    _sql, _resultSetType.intValue(), _resultSetConcurrency.intValue(),
                    _resultSetHoldability.intValue());
            return statement;
        }
    }

    /**
     * Builder for prepareStatement(String sql, String[] columnNames)
     */
    private class PreparedStatementWithColumnNames implements StatementBuilder {
        @Override
        public Statement createStatement(final Connection connection) throws SQLException {
            final PreparedStatement statement = connection.prepareStatement(
                    _sql, _columnNames);
            return statement;
        }
    }

    /**
     * Builder for prepareCall(String sql)
     */
    private class PreparedCallSQL implements StatementBuilder {
        @Override
        public Statement createStatement(final Connection connection) throws SQLException {
            final PreparedStatement statement = connection.prepareCall(_sql);
            return statement;
        }
    }

    /**
     * Builder for prepareCall(String sql, int resultSetType, int resultSetConcurrency)
     */
    private class PreparedCallWithResultSetConcurrency implements StatementBuilder {
        @Override
        public Statement createStatement(final Connection connection) throws SQLException {
            final PreparedStatement statement = connection.prepareCall(
                    _sql, _resultSetType.intValue(), _resultSetConcurrency.intValue());
            return statement;
        }
    }

    /**
     * Builder for prepareCall(String sql, int resultSetType, int resultSetConcurrency, int resultSetHoldability)
     */
    private class PreparedCallWithResultSetHoldability implements StatementBuilder {
        @Override
        public Statement createStatement(final Connection connection) throws SQLException {
            final PreparedStatement statement = connection.prepareCall(
                    _sql, _resultSetType.intValue(), _resultSetConcurrency.intValue(),
                    _resultSetHoldability.intValue());
            return statement;
        }
    }
}
