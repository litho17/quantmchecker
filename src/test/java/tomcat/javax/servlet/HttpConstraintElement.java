/*
* Licensed to the Apache Software Foundation (ASF) under one or more
* contributor license agreements.  See the NOTICE file distributed with
* this work for additional information regarding copyright ownership.
* The ASF licenses this file to You under the Apache License, Version 2.0
* (the "License"); you may not use this file except in compliance with
* the License.  You may obtain a copy of the License at
*
*     http://www.apache.org/licenses/LICENSE-2.0
*
* Unless required by applicable law or agreed to in writing, software
* distributed under the License is distributed on an "AS IS" BASIS,
* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
* See the License for the specific language governing permissions and
* limitations under the License.
*/
package tomcat.javax.servlet;

import tomcat.javax.servlet.annotation.HttpConstraint;
import tomcat.javax.servlet.annotation.ServletSecurity;

import java.util.ResourceBundle;

/**
 * Equivalent of {@link HttpConstraint} for
 * programmatic configuration of security constraints.
 *
 * @since Servlet 3.0
 */
public class HttpConstraintElement {

    private static final String LSTRING_FILE = "javax.servlet.LocalStrings";
    private static final ResourceBundle lStrings =
        ResourceBundle.getBundle(LSTRING_FILE);

    private final ServletSecurity.EmptyRoleSemantic emptyRoleSemantic;// = EmptyRoleSemantic.PERMIT;
    private final ServletSecurity.TransportGuarantee transportGuarantee;// = TransportGuarantee.NONE;
    private final String[] rolesAllowed;// = new String[0];

    /**
     * Default constraint is permit with no transport guarantee.
     */
    public HttpConstraintElement() {
        // Default constructor
        this.emptyRoleSemantic = ServletSecurity.EmptyRoleSemantic.PERMIT;
        this.transportGuarantee = ServletSecurity.TransportGuarantee.NONE;
        this.rolesAllowed = new String[0];
    }

    /**
     * Construct a constraint with an empty role semantic. Typically used with
     * {@link ServletSecurity.EmptyRoleSemantic#DENY}.
     *
     * @param emptyRoleSemantic The empty role semantic to apply to the newly
     *                          created constraint
     */
    public HttpConstraintElement(ServletSecurity.EmptyRoleSemantic emptyRoleSemantic) {
        this.emptyRoleSemantic = emptyRoleSemantic;
        this.transportGuarantee = ServletSecurity.TransportGuarantee.NONE;
        this.rolesAllowed = new String[0];
    }

    /**
     * Construct a constraint with a transport guarantee and roles.
     *
     * @param transportGuarantee The transport guarantee to apply to the newly
     *                           created constraint
     * @param rolesAllowed       The roles to associate with the newly created
     *                           constraint
     */
    public HttpConstraintElement(ServletSecurity.TransportGuarantee transportGuarantee,
            String... rolesAllowed) {
        this.emptyRoleSemantic = ServletSecurity.EmptyRoleSemantic.PERMIT;
        this.transportGuarantee = transportGuarantee;
        this.rolesAllowed = rolesAllowed;
    }

    /**
     * Construct a constraint with an empty role semantic, a transport guarantee
     * and roles.
     *
     * @param emptyRoleSemantic The empty role semantic to apply to the newly
     *                          created constraint
     * @param transportGuarantee The transport guarantee to apply to the newly
     *                           created constraint
     * @param rolesAllowed       The roles to associate with the newly created
     *                           constraint
     * @throws IllegalArgumentException if roles are specified when DENY is used
     */
    public HttpConstraintElement(ServletSecurity.EmptyRoleSemantic emptyRoleSemantic,
                                 ServletSecurity.TransportGuarantee transportGuarantee, String... rolesAllowed) {
        if (rolesAllowed != null && rolesAllowed.length > 0 &&
                ServletSecurity.EmptyRoleSemantic.DENY.equals(emptyRoleSemantic)) {
            throw new IllegalArgumentException(lStrings.getString(
                    "httpConstraintElement.invalidRolesDeny"));
        }
        this.emptyRoleSemantic = emptyRoleSemantic;
        this.transportGuarantee = transportGuarantee;
        this.rolesAllowed = rolesAllowed;
    }

    /**
     * TODO
     * @return TODO
     */
    public ServletSecurity.EmptyRoleSemantic getEmptyRoleSemantic() {
        return emptyRoleSemantic;
    }

    /**
     * TODO
     * @return TODO
     */
    public ServletSecurity.TransportGuarantee getTransportGuarantee() {
        return transportGuarantee;
    }

    /**
     * TODO
     * @return TODO
     */
    public String[] getRolesAllowed() {
        return rolesAllowed;
    }
}