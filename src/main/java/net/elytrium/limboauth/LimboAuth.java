/*
 * Copyright (C) 2021 - 2025 Elytrium
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package net.elytrium.limboauth;

import com.google.common.primitives.Bytes;
import com.google.common.primitives.Longs;
import com.google.inject.Inject;
import com.j256.ormlite.dao.Dao;
import com.j256.ormlite.dao.DaoManager;
import com.j256.ormlite.dao.GenericRawResults;
import com.j256.ormlite.db.DatabaseType;
import com.j256.ormlite.field.FieldType;
import com.j256.ormlite.stmt.QueryBuilder;
import com.j256.ormlite.stmt.UpdateBuilder;
import com.j256.ormlite.support.ConnectionSource;
import com.j256.ormlite.table.TableInfo;
import com.j256.ormlite.table.TableUtils;
import com.velocitypowered.api.command.CommandManager;
import com.velocitypowered.api.event.EventManager;
import com.velocitypowered.api.event.Subscribe;
import com.velocitypowered.api.event.proxy.ProxyInitializeEvent;
import com.velocitypowered.api.network.ProtocolVersion;
import com.velocitypowered.api.plugin.Dependency;
import com.velocitypowered.api.plugin.Plugin;
import com.velocitypowered.api.plugin.PluginContainer;
import com.velocitypowered.api.plugin.annotation.DataDirectory;
import com.velocitypowered.api.proxy.Player;
import com.velocitypowered.api.proxy.ProxyServer;
import com.velocitypowered.api.proxy.messages.ChannelIdentifier;
import com.velocitypowered.api.proxy.messages.LegacyChannelIdentifier;
import com.velocitypowered.api.proxy.messages.MinecraftChannelIdentifier;
import com.velocitypowered.api.scheduler.ScheduledTask;
import com.velocitypowered.proxy.util.ratelimit.Ratelimiter;
import com.velocitypowered.proxy.util.ratelimit.Ratelimiters;
import edu.umd.cs.findbugs.annotations.SuppressFBWarnings;
import io.whitfin.siphash.SipHasher;
import java.io.File;
import java.io.IOException;
import java.net.InetAddress;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URLEncoder;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.sql.SQLException;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.UUID;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import net.elytrium.commons.kyori.serialization.Serializer;
import net.elytrium.commons.kyori.serialization.Serializers;
import net.elytrium.commons.utils.reflection.ReflectionException;
import net.elytrium.commons.utils.updates.UpdatesChecker;
import net.elytrium.limboapi.api.Limbo;
import net.elytrium.limboapi.api.LimboFactory;
import net.elytrium.limboapi.api.chunk.VirtualWorld;
import net.elytrium.limboapi.api.command.LimboCommandMeta;
import net.elytrium.limboapi.api.file.WorldFile;
import net.elytrium.limboauth.command.*;
import net.elytrium.limboauth.dependencies.DatabaseLibrary;
import net.elytrium.limboauth.event.*;
import net.elytrium.limboauth.floodgate.FloodgateApiHolder;
import net.elytrium.limboauth.handler.AuthSessionHandler;
import net.elytrium.limboauth.listener.AuthListener;
import net.elytrium.limboauth.listener.BackendEndpointsListener;
import net.elytrium.limboauth.model.RegisteredPlayer;
import net.elytrium.limboauth.model.SQLRuntimeException;
import net.kyori.adventure.text.Component;
import net.kyori.adventure.text.serializer.ComponentSerializer;
import net.kyori.adventure.title.Title;
import org.bstats.charts.SimplePie;
import org.bstats.charts.SingleLineChart;
import org.bstats.velocity.Metrics;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.slf4j.Logger;

@Plugin(id = "limboauth", name = "LimboAuth", version = BuildConstants.AUTH_VERSION, url = "https://elytrium.net/",
        authors = {"Elytrium (https://elytrium.net/)"},
        dependencies = {@Dependency(id = "limboapi"), @Dependency(id = "floodgate", optional = true)})
public class LimboAuth {

    public static final Ratelimiter<InetAddress> RATELIMITER = Ratelimiters.createWithMilliseconds(5000);
    private static final ChannelIdentifier MOD_CHANNEL = MinecraftChannelIdentifier.create("limboauth", "mod/541f59e4256a337ea252bc482a009d46");
    private static final ChannelIdentifier LEGACY_MOD_CHANNEL = new LegacyChannelIdentifier("LIMBOAUTH|MOD");

    @MonotonicNonNull private static Logger LOGGER;
    @MonotonicNonNull private static Serializer SERIALIZER;

    private final Map<String, CachedSessionUser> cachedAuthChecks = new ConcurrentHashMap<>();
    private final Map<String, CachedPremiumUser> premiumCache = new ConcurrentHashMap<>();
    private final Map<InetAddress, CachedBruteforceUser> bruteforceCache = new ConcurrentHashMap<>();
    private final Map<UUID, Runnable> postLoginTasks = new ConcurrentHashMap<>();
    private final Set<String> unsafePasswords = new HashSet<>();
    private final Set<String> forcedPreviously = Collections.synchronizedSet(new HashSet<>());
    private final Set<String> pendingLogins = ConcurrentHashMap.newKeySet();

    private final HttpClient client = HttpClient.newHttpClient();
    private final ProxyServer server;
    private final Metrics.Factory metricsFactory;
    private final Path dataDirectory;
    private final File dataDirectoryFile;
    private final File configFile;
    private final LimboFactory factory;
    private final FloodgateApiHolder floodgateApi;
    private final Map<String, AuthSessionHandler> authenticatingPlayers;

    @Nullable private Component loginPremium;
    @Nullable private Title loginPremiumTitle;
    @Nullable private Component loginFloodgate;
    @Nullable private Title loginFloodgateTitle;
    private Component registrationsDisabledKick;
    private Component bruteforceAttemptKick;
    private Component nicknameInvalidKick;
    private Component reconnectKick;
    private ScheduledTask purgeCacheTask;
    private ScheduledTask purgePremiumCacheTask;
    private ScheduledTask purgeBruteforceCacheTask;

    private ConnectionSource connectionSource;
    private Dao<RegisteredPlayer, String> playerDao;
    private Pattern nicknameValidationPattern;
    private Limbo authServer;

    @Inject
    public LimboAuth(Logger logger, ProxyServer server, Metrics.Factory metricsFactory, @DataDirectory Path dataDirectory) {
        setLogger(logger);
        this.server = server;
        this.metricsFactory = metricsFactory;
        this.dataDirectory = dataDirectory;
        this.dataDirectoryFile = dataDirectory.toFile();
        this.configFile = new File(this.dataDirectoryFile, "config.yml");
        this.authenticatingPlayers = new ConcurrentHashMap<>();
        this.factory = (LimboFactory) this.server.getPluginManager().getPlugin("limboapi").flatMap(PluginContainer::getInstance).orElseThrow();
        this.floodgateApi = this.server.getPluginManager().getPlugin("floodgate").isPresent() ? new FloodgateApiHolder() : null;
    }

    @Subscribe
    public void onProxyInitialization(ProxyInitializeEvent event) {
        System.setProperty("com.j256.simplelogging.level", "ERROR");
        try {
            this.reload();
        } catch (SQLRuntimeException exception) {
            LOGGER.error("SQL EXCEPTION CAUGHT.", exception);
            this.server.shutdown();
        }

        Metrics metrics = this.metricsFactory.make(this, 13700);
        metrics.addCustomChart(new SimplePie("floodgate_auth", () -> String.valueOf(Settings.IMP.MAIN.FLOODGATE_NEED_AUTH)));
        metrics.addCustomChart(new SimplePie("premium_auth", () -> String.valueOf(Settings.IMP.MAIN.ONLINE_MODE_NEED_AUTH)));
        metrics.addCustomChart(new SimplePie("db_type", () -> String.valueOf(Settings.IMP.DATABASE.STORAGE_TYPE)));
        metrics.addCustomChart(new SimplePie("load_world", () -> String.valueOf(Settings.IMP.MAIN.LOAD_WORLD)));
        metrics.addCustomChart(new SimplePie("totp_enabled", () -> String.valueOf(Settings.IMP.MAIN.ENABLE_TOTP)));
        metrics.addCustomChart(new SimplePie("dimension", () -> String.valueOf(Settings.IMP.MAIN.DIMENSION)));
        metrics.addCustomChart(new SimplePie("save_uuid", () -> String.valueOf(Settings.IMP.MAIN.SAVE_UUID)));
        metrics.addCustomChart(new SingleLineChart("registered_players", () -> Math.toIntExact(this.playerDao.countOf())));
    }

    public void reload() {
        Settings.IMP.reload(this.configFile, Settings.IMP.PREFIX);
        AuthSessionHandler.reload();
        // ... (Include your existing reload logic here)
    }

    public void cacheAuthUser(Player player) {
        String username = player.getUsername();
        String lowercaseUsername = username.toLowerCase(Locale.ROOT);
        this.cachedAuthChecks.put(lowercaseUsername, new CachedSessionUser(System.currentTimeMillis(), player.getRemoteAddress().getAddress(), username));
    }

    public void removeAuthenticatingPlayer(String nickname) {
        this.authenticatingPlayers.remove(nickname);
    }

    public void addAuthenticatingPlayer(String nickname, AuthSessionHandler handler) {
        this.authenticatingPlayers.put(nickname, handler);
    }
    
    public void incrementBruteforceAttempts(InetAddress address) {
        this.getBruteforceUser(address).incrementAttempts();
    }

    public int getBruteforceAttempts(InetAddress address) {
        return this.getBruteforceUser(address).getAttempts();
    }

    private CachedBruteforceUser getBruteforceUser(InetAddress address) {
        CachedBruteforceUser user = this.bruteforceCache.get(address);
        if (user == null) {
            user = new CachedBruteforceUser(System.currentTimeMillis());
            this.bruteforceCache.put(address, user);
        }
        return user;
    }

    public void clearBruteforceAttempts(InetAddress address) {
        this.bruteforceCache.remove(address);
    }

    private static void setLogger(Logger logger) { LOGGER = logger; }
    private static void setSerializer(Serializer serializer) { SERIALIZER = serializer; }
    public static Serializer getSerializer() { return SERIALIZER; }
    
    // --- INNER CLASSES ---

    public static class CachedUser {
        private final long checkTime;
        public CachedUser(long checkTime) { this.checkTime = checkTime; }
        public long getCheckTime() { return this.checkTime; }
    }

    private static class CachedSessionUser extends CachedUser {
        private final InetAddress inetAddress;
        private final String username;
        public CachedSessionUser(long checkTime, InetAddress inetAddress, String username) {
            super(checkTime);
            this.inetAddress = inetAddress;
            this.username = username;
        }
        public InetAddress getInetAddress() { return this.inetAddress; }
        public String getUsername() { return this.username; }
    }

    public static class CachedPremiumUser extends CachedUser {
        private final boolean premium;
        private boolean forcePremium;
        public CachedPremiumUser(long checkTime, boolean premium) {
            super(checkTime);
            this.premium = premium;
        }
        public void setForcePremium(boolean forcePremium) { this.forcePremium = forcePremium; }
        public boolean isForcePremium() { return this.forcePremium; }
        public boolean isPremium() { return this.premium; }
    }

    private static class CachedBruteforceUser extends CachedUser {
        private int attempts;
        public CachedBruteforceUser(long checkTime) { super(checkTime); }
        public void incrementAttempts() { this.attempts++; }
        public int getAttempts() { return this.attempts; }
    }
}
