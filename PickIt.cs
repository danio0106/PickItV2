using ExileCore;
using ExileCore.PoEMemory.Components;
using ExileCore.PoEMemory.Elements;
using ExileCore.PoEMemory.MemoryObjects;
using ExileCore.Shared;
using ExileCore.Shared.Cache;
using ExileCore.Shared.Enums;
using ExileCore.Shared.Helpers;
using ItemFilterLibrary;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using System.Windows.Forms;
using ExileCore.PoEMemory;
using SharpDX;
using SDxVector2 = SharpDX.Vector2;
using Vector2 = System.Numerics.Vector2;
using Vector3 = System.Numerics.Vector3;

namespace PickIt;

public partial class PickIt : BaseSettingsPlugin<PickItSettings>
{
    private readonly CachedValue<List<LabelOnGround>> _chestLabels;
    private readonly CachedValue<LabelOnGround> _portalLabel;
    private readonly CachedValue<int[,]> _inventorySlotsWithItemIds;
    private ServerInventory _inventoryItems;
    private SyncTask<bool> _pickUpTask;
    public List<ItemFilter> ItemFilters;
    private bool _pluginBridgeModeOverride;
    public static PickIt Main;
    private readonly Stopwatch _sinceLastClick = Stopwatch.StartNew();
    private readonly ConditionalWeakTable<string, Regex> _regexes = [];
    private readonly Dictionary<long, DateTime> _recentPickupAttempts = [];
    private bool _warnedMissingMagicInput;
    private bool _warnedMagicInputFailed;
    private bool? _magicInputAvailable;
    private DateTime _nextMagicInputProbeAt = DateTime.MinValue;
    private Action<Entity, uint> _cachedMagicInputCast;
    private DateTime _lastEmergencyUnblockLogAt = DateTime.MinValue;
    private DateTime _preserveLeftMouseIntentTill = DateTime.MinValue;
    private DateTime _restoreHeldLeftMouseTill = DateTime.MinValue;

    public PickIt()
    {
        Name = "PickIt With Linq";
        _inventorySlotsWithItemIds = new FrameCache<int[,]>(() => GetContainer2DArrayWithItemIds(_inventoryItems));
        _chestLabels = new TimeCache<List<LabelOnGround>>(UpdateChestList, 200);
        _portalLabel = new TimeCache<LabelOnGround>(() => GetLabel(@"^Metadata/(MiscellaneousObjects|Effects/Microtransactions)/.*Portal"), 200);
    }

    public override bool Initialise()
    {
        Main = this;

        #region Register keys

        Settings.PickUpKey.OnValueChanged += () => Input.RegisterKey(Settings.PickUpKey);
        Settings.ProfilerHotkey.OnValueChanged += () => Input.RegisterKey(Settings.ProfilerHotkey);

        Input.RegisterKey(Settings.PickUpKey);
        Input.RegisterKey(Settings.ProfilerHotkey);
        Input.RegisterKey(Keys.Escape);

        #endregion
        
        RulesDisplay.LoadAndApplyRules();
        GameController.PluginBridge.SaveMethod("PickIt.ListItems", () => GetItemsToPickup(false).Select(x => x.QueriedItem).ToList());
        GameController.PluginBridge.SaveMethod("PickIt.IsActive", () => _pickUpTask?.GetAwaiter().IsCompleted == false);
        GameController.PluginBridge.SaveMethod("PickIt.SetWorkMode", (bool running) => { _pluginBridgeModeOverride = running; });

        if (Settings.UseMagicInput.Value)
        {
            var startupMagicInputCast = GetMagicInputCastIfAvailable();
            if (startupMagicInputCast != null)
            {
                DebugWindow.LogMsg("[PickIt] Startup MagicInput probe: bridge available.", 10);
            }
            else
            {
                DebugWindow.LogError("[PickIt] Startup MagicInput probe: bridge unavailable.", 10);
            }
        }

        return true;
    }

    private enum WorkMode
    {
        Stop,
        Lazy,
        Manual
    }

    private bool ShouldExecute()
    {
        if (!GameController.Window.IsForeground())
        {
            _pluginBridgeModeOverride = false;
            return false;
        }

        if (GameController.Game.IsEscapeState || Input.GetKeyState(Keys.Escape))
        {
            _pluginBridgeModeOverride = false;
            return false;
        }

        if (Input.GetKeyState(Keys.Menu) || Input.GetKeyState(Keys.LMenu) || Input.GetKeyState(Keys.RMenu))
        {
            _pluginBridgeModeOverride = false;
            return false;
        }

        if (!GameController.Player.TryGetComponent<Life>(out var lifeComponent) || lifeComponent.CurHP <= 0)
        {
            _pluginBridgeModeOverride = false;
            return false;
        }

        if (!GameController.Player.TryGetComponent<Buffs>(out var buffsComponent))
        {
            _pluginBridgeModeOverride = false;
            return false;
        }

        if (buffsComponent.HasBuff("grace_period"))
        {
            _pluginBridgeModeOverride = false;
            return false;
        }

        if (!GameController.Player.HasComponent<Actor>())
        {
            _pluginBridgeModeOverride = false;
            return false;
        }

        return true;
    }

    private WorkMode GetWorkMode()
    {
        if (!Settings.Enable || !ShouldExecute())
        {
            return WorkMode.Stop;
        }

        if (Input.GetKeyState(Settings.ProfilerHotkey.Value))
        {
            var sw = Stopwatch.StartNew();
            var looseVar2 = GetItemsToPickup(false).FirstOrDefault();
            sw.Stop();
            LogMessage($"GetItemsToPickup Elapsed Time: {sw.ElapsedTicks} Item: {looseVar2?.BaseName} Distance: {looseVar2?.Distance}");
        }

        if (Input.GetKeyState(Settings.PickUpKey.Value) || _pluginBridgeModeOverride)
        {
            return WorkMode.Manual;
        }

        if (CanLazyLoot())
        {
            return WorkMode.Lazy;
        }

        return WorkMode.Stop;
    }

    private DateTime DisableLazyLootingTill { get; set; }

    public override Job Tick()
    {
        TryEmergencyReleaseInputBlock();

        var playerInvCount = GameController?.Game?.IngameState?.Data?.ServerData?.PlayerInventories?.Count;
        if (playerInvCount is null or 0)
            return null;

        _inventoryItems = GameController.Game.IngameState.Data.ServerData.PlayerInventories[0].Inventory;
        if (Input.GetKeyState(Settings.LazyLootingPauseKey)) DisableLazyLootingTill = DateTime.Now.AddSeconds(2);
        if (Input.GetKeyState(Keys.LButton)) _preserveLeftMouseIntentTill = DateTime.Now.AddMilliseconds(350);

        if (_mouseBlockHookHandle != IntPtr.Zero && DateTime.Now > _mouseBlockFailsafeUntil)
        {
            EndBlockMouseInput();
        }

        return null;
    }

    public override void Render()
    {
        DrawInventoryCells();

        if (Input.GetKeyState(Keys.LButton))
        {
            _preserveLeftMouseIntentTill = DateTime.Now.AddMilliseconds(350);
        }

        // Re-assert held LMB for a short window after pickup clicks when pickup started with LMB held.
        if (_forceRestoreLeftMouseTill > DateTime.Now &&
            _preserveLeftMouseIntentTill > DateTime.Now &&
            _restoreHeldLeftMouseTill > DateTime.Now &&
            !Input.IsKeyDown(Keys.LButton))
        {
            Input.LeftDown();
        }

        if (Settings.DebugHighlight)
        {
            foreach (var item in GetItemsToPickup(false))
            {
                Graphics.DrawFrame(item.QueriedItem.ClientRect, Color.Violet, 5);
            }
        }

        if (GetWorkMode() != WorkMode.Stop)
        {
            TaskUtils.RunOrRestart(ref _pickUpTask, RunPickerIterationAsync);
        }
        else
        {
            _pickUpTask = null;
        }

        if (Settings.FilterTest.Value is { Length: > 0 } &&
            GameController.IngameState.UIHover is { Address: not 0 } h &&
            h.Entity.IsValid)
        {
            var f = ItemFilter.LoadFromString(Settings.FilterTest);
            var matched = f.Matches(new ItemData(h.Entity, GameController));
            DebugWindow.LogMsg($"Debug item match: {matched}");
        }
    }

    private void DrawInventoryCells()
    {
        var settings = Settings.InventoryRender;
        if (!settings.ShowInventoryView.Value)
            return;

        var ingameUi = GameController.Game.IngameState.IngameUi;
        if (!settings.IgnoreFullscreenPanels && ingameUi.FullscreenPanels.Any(x => x.IsVisible))
            return;

        if (!settings.IgnoreLargePanels && ingameUi.LargePanels.Any(x => x.IsVisible))
            return;

        if (!settings.IgnoreChatPanel && ingameUi.ChatTitlePanel.IsVisible)
            return;

        if (!settings.IgnoreLeftPanel && ingameUi.OpenLeftPanel.IsVisible)
            return;

        if (!settings.IgnoreRightPanel && ingameUi.OpenRightPanel.IsVisible)
            return;

        var windowSize = GameController.Window.GetWindowRectangleTimeCache;
        var inventoryItemIds = _inventorySlotsWithItemIds.Value;
        if (inventoryItemIds == null)
            return;

        var viewTopLeftX = (int)(windowSize.Width * (settings.Position.Value.X / 100f));
        var viewTopLeftY = (int)(windowSize.Height * (settings.Position.Value.Y / 100f));

        var cellSize = settings.CellSize;
        var cellSpacing = settings.CellSpacing;
        var outlineWidth = settings.ItemOutlineWidth;
        var backerPadding = settings.BackdropPadding;

        var inventoryRows = inventoryItemIds.GetLength(0);
        var inventoryCols = inventoryItemIds.GetLength(1);
        var gridWidth = inventoryCols * (cellSize + cellSpacing) - cellSpacing;
        var gridHeight = inventoryRows * (cellSize + cellSpacing) - cellSpacing;
        var backerRect = new RectangleF(
            viewTopLeftX - backerPadding, viewTopLeftY - backerPadding, gridWidth + backerPadding * 2, gridHeight + backerPadding * 2);
        Graphics.DrawBox(backerRect, settings.BackgroundColor.Value);

        var itemBounds = new Dictionary<int, (int MinX, int MinY, int MaxX, int MaxY)>();
        for (var y = 0; y < inventoryRows; y++)
        for (var x = 0; x < inventoryCols; x++)
        {
            var isOccupied = inventoryItemIds[y, x] > 0;
            var cellColor = isOccupied ? settings.OccupiedSlotColor.Value : settings.UnoccupiedSlotColor.Value;
            var cellX = viewTopLeftX + x * (cellSize + cellSpacing);
            var cellY = viewTopLeftY + y * (cellSize + cellSpacing);
            var cellRect = new RectangleF(cellX, cellY, cellSize, cellSize);
            Graphics.DrawBox(cellRect, cellColor);

            var itemId = inventoryItemIds[y, x];
            if (itemId == 0) continue;

            if (itemBounds.TryGetValue(itemId, out var bounds))
            {
                bounds.MinX = Math.Min(bounds.MinX, x);
                bounds.MinY = Math.Min(bounds.MinY, y);
                bounds.MaxX = Math.Max(bounds.MaxX, x);
                bounds.MaxY = Math.Max(bounds.MaxY, y);
                itemBounds[itemId] = bounds;
            }
            else
            {
                itemBounds[itemId] = (x, y, x, y);
            }
        }

        foreach (var (_, (minX, minY, maxX, maxY)) in itemBounds)
        {
            var itemAreaX = viewTopLeftX + minX * (cellSize + cellSpacing);
            var itemAreaY = viewTopLeftY + minY * (cellSize + cellSpacing);
            var itemAreaWidth = (maxX - minX + 1) * (cellSize + cellSpacing) - cellSpacing;
            var itemAreaHeight = (maxY - minY + 1) * (cellSize + cellSpacing) - cellSpacing;

            var outerRect = new RectangleF(itemAreaX, itemAreaY, itemAreaWidth, itemAreaHeight);
            DrawFrameInside(outerRect, outlineWidth, settings.ItemOutlineColor.Value);
        }

        return;

        void DrawFrameInside(RectangleF outerRect, int thickness, Color color)
        {
            // A horrible workaround to the uneven values set by users resulting in not pixel perfect drawing
            if (thickness <= 0) return;
            // Top
            Graphics.DrawBox(new RectangleF(outerRect.Left, outerRect.Top, outerRect.Width, thickness), color);
            // Bottom
            Graphics.DrawBox(new RectangleF(outerRect.Left, outerRect.Bottom - thickness, outerRect.Width, thickness), color);
            // Left
            Graphics.DrawBox(new RectangleF(outerRect.Left, outerRect.Top + thickness, thickness, outerRect.Height - thickness * 2), color);
            // Right
            Graphics.DrawBox(new RectangleF(outerRect.Right - thickness, outerRect.Top + thickness, thickness, outerRect.Height - thickness * 2), color);
        }
    }

    private bool DoWePickThis(PickItItemData item)
    {
        return Settings.PickUpEverything || (ItemFilters?.Any(filter => filter.Matches(item)) ?? false);
    }

    private bool WasRecentlyAttempted(Entity entity)
    {
        if (entity?.Address is not > 0)
        {
            return false;
        }

        if (_recentPickupAttempts.TryGetValue(entity.Address, out var retryUntil))
        {
            if (retryUntil > DateTime.Now)
            {
                return true;
            }

            _recentPickupAttempts.Remove(entity.Address);
        }

        return false;
    }

    private void RememberAttempt(Entity entity, int retryDelayMs = 600)
    {
        if (entity?.Address is not > 0)
        {
            return;
        }

        _recentPickupAttempts[entity.Address] = DateTime.Now.AddMilliseconds(retryDelayMs);
    }

    private List<LabelOnGround> UpdateChestList()
    {
        bool IsKnownDelveNpcInteractable(Entity entity)
        {
            var metadata = entity.Metadata ?? string.Empty;

            // Real Delve interactables on NPC paths should behave like world objects, not actors/NPCs.
            if (entity.HasComponent<Actor>())
            {
                return false;
            }

            if (metadata.Contains("AzuriteVein", StringComparison.OrdinalIgnoreCase) ||
                metadata.Contains("DelveMinerWildVein", StringComparison.OrdinalIgnoreCase))
            {
                return entity.HasComponent<Targetable>();
            }

            if (metadata.Contains("DelveMinerWildChest", StringComparison.OrdinalIgnoreCase))
            {
                return entity.HasComponent<Chest>();
            }

            return false;
        }

        bool IsKnownDelveInteractable(Entity entity)
        {
            var metadata = entity.Metadata ?? string.Empty;

            return IsKnownDelveNpcInteractable(entity) ||
                                     metadata.StartsWith("Metadata/Chests/DelveChests/", StringComparison.OrdinalIgnoreCase);
        }

        bool IsFittingEntity(Entity entity)
        {
            if (string.IsNullOrEmpty(entity.Metadata))
            {
                return false;
            }

            // Never target NPC metadata, except explicit Delve interactables that are not real town/quest NPCs.
            if (entity.Metadata.StartsWith("Metadata/NPC/", StringComparison.OrdinalIgnoreCase) &&
                !IsKnownDelveInteractable(entity))
            {
                return false;
            }

            var matchedRule = Settings.ChestSettings.ChestList.Content.FirstOrDefault(
                x => x.Enabled?.Value == true &&
                     !string.IsNullOrEmpty(x.MetadataRegex?.Value) &&
                     _regexes.GetValue(x.MetadataRegex.Value, p => new Regex(p))!.IsMatch(entity.Metadata));

            // Allow known Delve interactables (chests + veins) even when no explicit rule matches.
            // The NPC guard above already prevents non-Delve NPCs from reaching here.
            if (matchedRule == null)
            {
                if (IsKnownDelveInteractable(entity))
                {
                    return true;
                }

                return false;
            }

            if (entity.HasComponent<Chest>())
            {
                return true;
            }

            // Delve targets (veins/resonator-like objects) can be non-Chest entities.
            return matchedRule.MetadataRegex.Value.Contains("Delve", StringComparison.OrdinalIgnoreCase);
        }

        if (GameController.EntityListWrapper.OnlyValidEntities.Any(IsFittingEntity))
        {
            return GameController?.Game?.IngameState?.IngameUi?.ItemsOnGroundLabelsVisible
                .Where(x => x.Address != 0 &&
                            x.IsVisible &&
                            IsFittingEntity(x.ItemOnGround))
                .OrderBy(x => x.ItemOnGround.DistancePlayer)
                .ToList() ?? [];
        }

        return [];
    }

    private bool CanLazyLoot()
    {
        if (!Settings.LazyLooting) return false;
        if (DisableLazyLootingTill > DateTime.Now) return false;
        try
        {
            if (Settings.NoLazyLootingWhileEnemyClose && GameController.EntityListWrapper.ValidEntitiesByType[EntityType.Monster]
                    .Any(x => x?.GetComponent<Monster>() != null && x.IsValid && x.IsHostile && x.IsAlive
                              && !x.IsHidden && !x.Path.Contains("ElementalSummoned")
                              && Vector3.Distance(GameController.Player.PosNum, x.GetComponent<Render>().PosNum) < Settings.PickupRange)) return false;
        }
        catch (NullReferenceException)
        {
        }

        return true;
    }

    private bool ShouldLazyLoot(PickItItemData item)
    {
        if (item == null)
        {
            return false;
        }

        return IsEntityInLazyLootRange(item.QueriedItem.Entity);
    }

    private bool IsEntityInLazyLootRange(Entity entity)
    {
        if (entity == null)
        {
            return false;
        }

        var itemPos = entity.PosNum;
        var playerPos = GameController.Player.PosNum;
        return Math.Abs(itemPos.Z - playerPos.Z) <= 50 &&
               itemPos.Xy().DistanceSquared(playerPos.Xy()) <= 275 * 275;
    }

    private bool IsLabelClickable(Element element, RectangleF? customRect)
    {
        if (element is not { IsValid: true, IsVisible: true, IndexInParent: not null })
        {
            return false;
        }

        var center = (customRect ?? element.GetClientRect()).Center;

        var gameWindowRect = GameController.Window.GetWindowRectangleTimeCache with { Location = SDxVector2.Zero };
        gameWindowRect.Inflate(-36, -36);
        return gameWindowRect.Contains(center.X, center.Y);
    }

    private bool IsPortalTargeted(LabelOnGround portalLabel)
    {
        if (portalLabel == null)
        {
            return false;
        }

        // extra checks in case of HUD/game update. They are easy on CPU
        return
            GameController.IngameState.UIHover.Address == portalLabel.Address ||
            GameController.IngameState.UIHover.Address == portalLabel.ItemOnGround.Address ||
            GameController.IngameState.UIHover.Address == portalLabel.Label.Address ||
            GameController.IngameState.UIHoverElement.Address == portalLabel.Address ||
            GameController.IngameState.UIHoverElement.Address == portalLabel.ItemOnGround.Address ||
            GameController.IngameState.UIHoverElement.Address ==
            portalLabel.Label.Address || // this is the right one
            GameController.IngameState.UIHoverTooltip.Address == portalLabel.Address ||
            GameController.IngameState.UIHoverTooltip.Address == portalLabel.ItemOnGround.Address ||
            GameController.IngameState.UIHoverTooltip.Address == portalLabel.Label.Address ||
            portalLabel.ItemOnGround?.HasComponent<Targetable>() == true &&
            portalLabel.ItemOnGround?.GetComponent<Targetable>()?.isTargeted == true;
    }

    private static bool IsPortalNearby(LabelOnGround portalLabel, Element element)
    {
        if (portalLabel == null) return false;
        var rect1 = portalLabel.Label.GetClientRectCache;
        var rect2 = element.GetClientRectCache;
        rect1.Inflate(100, 100);
        rect2.Inflate(100, 100);
        return rect1.Intersects(rect2);
    }

    private LabelOnGround GetLabel(string id)
    {
        var labels = GameController?.Game?.IngameState?.IngameUi?.ItemsOnGroundLabels;
        if (labels == null)
        {
            return null;
        }

        var regex = new Regex(id);
        var labelQuery =
            from labelOnGround in labels
            where labelOnGround?.Label is { IsValid: true, Address: > 0, IsVisible: true }
            let itemOnGround = labelOnGround.ItemOnGround
            where itemOnGround?.Metadata is { } metadata && regex.IsMatch(metadata)
            let dist = GameController?.Player?.GridPosNum.DistanceSquared(itemOnGround.GridPosNum)
            orderby dist
            select labelOnGround;

        return labelQuery.FirstOrDefault();
    }

    private const int WH_MOUSE_LL = 14;
    private const uint LLMHF_INJECTED = 0x00000001;
    private delegate IntPtr LowLevelMouseProc(int nCode, IntPtr wParam, IntPtr lParam);
    private LowLevelMouseProc _mouseBlockHookDelegate;
    private IntPtr _mouseBlockHookHandle = IntPtr.Zero;
    private DateTime _mouseBlockFailsafeUntil = DateTime.MinValue;

    [DllImport("user32.dll", SetLastError = true)]
    private static extern IntPtr SetWindowsHookEx(int idHook, LowLevelMouseProc lpfn, IntPtr hMod, uint dwThreadId);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern bool UnhookWindowsHookEx(IntPtr hhk);

    [DllImport("user32.dll")]
    private static extern IntPtr CallNextHookEx(IntPtr hhk, int nCode, IntPtr wParam, IntPtr lParam);

    [System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.Sequential)]
    private struct POINT { public int X; public int Y; }

    [System.Runtime.InteropServices.StructLayout(System.Runtime.InteropServices.LayoutKind.Sequential)]
    private struct MSLLHOOKSTRUCT
    {
        public POINT Pt;
        public uint MouseData;
        public uint Flags;
        public uint Time;
        public IntPtr DwExtraInfo;
    }

    [DllImport("user32.dll")]
    private static extern bool GetCursorPos(out POINT lpPoint);

    [DllImport("user32.dll")]
    private static extern bool SetCursorPos(int x, int y);

    
    [DllImport("user32.dll")]
    private static extern short GetAsyncKeyState(int vKey);

    private static bool IsPhysicalLeftMouseDown()
    {
        const int vkLButton = 0x01;
        return (GetAsyncKeyState(vkLButton) & 0x8000) != 0;
    }

    private void EnsureLeftMouseUpIfNotPhysicallyHeld()
    {
        if (!Settings.UnclickLeftMouseButton)
        {
            return;
        }

        if (!IsPhysicalLeftMouseDown() && Input.IsKeyDown(Keys.LButton))
        {
            Input.LeftUp();
        }
    }

    private void TryEmergencyReleaseInputBlock()
    {
        if (_mouseBlockHookHandle == IntPtr.Zero)
        {
            return;
        }

        if (!Input.GetKeyState(Keys.Escape))
        {
            return;
        }

        EndBlockMouseInput();
        _pluginBridgeModeOverride = false;
        DisableLazyLootingTill = DateTime.Now.AddSeconds(2);

        if (DateTime.Now > _lastEmergencyUnblockLogAt.AddMilliseconds(500))
        {
            LogMessage("[PickIt] Emergency input unblock triggered by Escape.");
            _lastEmergencyUnblockLogAt = DateTime.Now;
        }
    }

    private Action<Entity, uint> GetMagicInputCastIfAvailable()
    {
        var now = DateTime.Now;
        if (_cachedMagicInputCast != null && _nextMagicInputProbeAt > now)
        {
            return _cachedMagicInputCast;
        }

        _nextMagicInputProbeAt = now.AddMilliseconds(500);
        var resolved = GameController.PluginBridge.GetMethod<Action<Entity, uint>>("MagicInput.CastSkillWithTarget");
        var availableNow = resolved != null;

        if (_magicInputAvailable != availableNow)
        {
            if (availableNow)
            {
                LogMessage("[PickIt] MagicInput bridge is available.");
                DebugWindow.LogMsg("[PickIt] MagicInput bridge is available.", 10);
            }
            else
            {
                LogMessage("[PickIt] MagicInput bridge is unavailable. Falling back to mouse input.");
                DebugWindow.LogError("[PickIt] MagicInput bridge is unavailable. Falling back to mouse input.", 10);
            }

            _magicInputAvailable = availableNow;
        }

        _cachedMagicInputCast = resolved;
        return _cachedMagicInputCast;
    }

    private IntPtr MouseBlockCallback(int nCode, IntPtr wParam, IntPtr lParam)
    {
        if (nCode >= 0)
        {
            var hookData = Marshal.PtrToStructure<MSLLHOOKSTRUCT>(lParam);
            var isInjected = (hookData.Flags & LLMHF_INJECTED) != 0;

            // Block only physical mouse input from the user.
            // Allow injected input so PickIt's own Input.Click/SetCursorPos keeps working.
            if (!isInjected)
            {
                return (IntPtr)1;
            }
        }

        return CallNextHookEx(_mouseBlockHookHandle, nCode, wParam, lParam);
    }

    private bool BeginBlockMouseInput()
    {
        if (_mouseBlockHookHandle != IntPtr.Zero) return false;
        _mouseBlockHookDelegate = MouseBlockCallback;
        _mouseBlockHookHandle = SetWindowsHookEx(WH_MOUSE_LL, _mouseBlockHookDelegate, IntPtr.Zero, 0);
        if (_mouseBlockHookHandle != IntPtr.Zero)
        {
            _mouseBlockFailsafeUntil = DateTime.Now.AddSeconds(2);
        }
        return _mouseBlockHookHandle != IntPtr.Zero;
    }

    private void EndBlockMouseInput()
    {
        if (_mouseBlockHookHandle == IntPtr.Zero) return;
        UnhookWindowsHookEx(_mouseBlockHookHandle);
        _mouseBlockHookHandle = IntPtr.Zero;
        _mouseBlockFailsafeUntil = DateTime.MinValue;
    }

    private bool _isPickingUp = false;
    private DateTime _forceRestoreLeftMouseTill = DateTime.MinValue;
    private async SyncTask<bool> RunPickerIterationAsync()
    {
        _isPickingUp = false;
        try
        {
            if (!GameController.Window.IsForeground()) return true;

            var pickUpThisItem = GetItemsToPickup(true).FirstOrDefault();

            var workMode = GetWorkMode();
            if (workMode == WorkMode.Manual || workMode == WorkMode.Lazy)
            {
                if (Settings.ChestSettings.ClickChests)
                {
                    var chestLabel = _chestLabels?.Value.FirstOrDefault(x =>
                        x.ItemOnGround.DistancePlayer < Settings.PickupRange &&
                        IsLabelClickable(x.Label, null));

                    if (chestLabel != null)
                    {
                        var chestAllowedByMode = workMode == WorkMode.Manual || IsEntityInLazyLootRange(chestLabel.ItemOnGround);
                        if (chestAllowedByMode)
                        {
                            var isDelveChest = chestLabel.ItemOnGround.Metadata?.StartsWith("Metadata/Chests/DelveChests/", StringComparison.OrdinalIgnoreCase) == true;
                            var shouldPickChest = pickUpThisItem == null ||
                                                  isDelveChest ||
                                                  Settings.ChestSettings.TargetNearbyChestsFirst && chestLabel.ItemOnGround.DistancePlayer < Settings.ChestSettings.TargetNearbyChestsFirstRadius ||
                                                  pickUpThisItem.Distance >= chestLabel.ItemOnGround.DistancePlayer;

                            if (shouldPickChest)
                            {
                                await PickAsync(chestLabel.ItemOnGround, chestLabel.Label, null, _chestLabels.ForceUpdate, workMode == WorkMode.Lazy);
                                return true;
                            }
                        }
                    }
                }

                var shouldPickItem = workMode == WorkMode.Manual || ShouldLazyLoot(pickUpThisItem);
                if (!shouldPickItem)
                {
                    return true;
                }

                if (pickUpThisItem == null)
                {
                    return true;
                }

                var didAttemptClick = await PickAsync(pickUpThisItem.QueriedItem.Entity, pickUpThisItem.QueriedItem.Label, pickUpThisItem.QueriedItem.ClientRect, () => { }, workMode == WorkMode.Lazy);
                RememberAttempt(pickUpThisItem.QueriedItem.Entity, didAttemptClick ? 450 : 1200);
            }
        }
        finally
        {
            _isPickingUp = false;
        }

        return true;
    }

    private IEnumerable<PickItItemData> GetItemsToPickup(bool filterAttempts)
    {
        var labels = GameController.Game.IngameState.IngameUi.ItemsOnGroundLabelElement.VisibleGroundItemLabels?
            .Where(x=> x.Entity?.DistancePlayer is {} distance && distance < Settings.PickupRange)
            .OrderBy(x => x.Entity?.DistancePlayer ?? int.MaxValue);

        return labels?
            .Where(x => x.Entity?.Path != null && IsLabelClickable(x.Label, x.ClientRect))
            .Select(x => new PickItItemData(x, GameController))
            .Where(x => x.Entity != null
                        && (!filterAttempts || !WasRecentlyAttempted(x.Entity))
                        && DoWePickThis(x)
                        && (Settings.PickUpWhenInventoryIsFull || CanFitInventory(x))) ?? [];
    }

    private async SyncTask<bool> PickAsync(Entity item, Element label, RectangleF? customRect, Action onNonClickable, bool isLazyWorkMode)
    {
        _isPickingUp = true;
        EnsureLeftMouseUpIfNotPhysicallyHeld();
        var didAttemptClick = false;
        var leftMouseHeldAtStart = IsPhysicalLeftMouseDown();
        var restoreLeftMouseAfterPickup = Settings.UnclickLeftMouseButton && leftMouseHeldAtStart;
        if (restoreLeftMouseAfterPickup)
        {
            _restoreHeldLeftMouseTill = DateTime.Now.AddMilliseconds(1200);
            _preserveLeftMouseIntentTill = DateTime.Now.AddMilliseconds(700);
            Input.LeftUp();
        }

        var inputBlocked = Settings.BlockInputWhilePickingUp.Value && BeginBlockMouseInput();
        GetCursorPos(out var cursorSnapshot);
        var tryCount = 0;
        var hoverAttemptsWithoutTarget = 0;
        try
        {
            while (tryCount < 3)
            {
                TryEmergencyReleaseInputBlock();

                // Keep lazy-looting pause hotkey responsive, even mid-pick attempt.
                if (Input.GetKeyState(Settings.LazyLootingPauseKey))
                {
                    DisableLazyLootingTill = DateTime.Now.AddSeconds(2);
                    return true;
                }

                // Avoid stale click attempts if the item is no longer in lazy-loot range.
                if (isLazyWorkMode && !IsEntityInLazyLootRange(item))
                {
                    return true;
                }

                if (!IsLabelClickable(label, customRect))
                {
                    onNonClickable();
                    return true;
                }

                var shouldRespectMovementCheck = !Settings.IgnoreMoving && (!isLazyWorkMode || !Settings.IgnoreMovingInLazyLooting);
                if (shouldRespectMovementCheck && GameController.Player.GetComponent<Actor>().isMoving)
                {
                    if (item.DistancePlayer > Settings.ItemDistanceToIgnoreMoving.Value)
                    {
                        await TaskUtils.NextFrame();
                        continue;
                    }
                }

                var useMagicInput = Settings.UseMagicInput.Value;
                var magicInputCast = useMagicInput ? GetMagicInputCastIfAvailable() : null;

                if (useMagicInput && magicInputCast == null)
                {
                    if (!_warnedMissingMagicInput)
                    {
                        DebugWindow.LogError("[PickIt] UseMagicInput is enabled, but MagicInput.CastSkillWithTarget was not found. Falling back to mouse input.", 10);
                        _warnedMissingMagicInput = true;
                    }

                    useMagicInput = false;
                }

                if (useMagicInput)
                {
                    var canAttemptMagicClick = tryCount == 0 || _sinceLastClick.ElapsedMilliseconds >= Settings.PauseBetweenClicks;
                    if (!canAttemptMagicClick)
                    {
                        await TaskUtils.NextFrame();
                        continue;
                    }

                    EnsureLeftMouseUpIfNotPhysicallyHeld();

                    try
                    {
                        magicInputCast!(item, 0x400);
                    }
                    catch (Exception ex)
                    {
                        if (!_warnedMagicInputFailed)
                        {
                            DebugWindow.LogError($"[PickIt] MagicInput call failed: {ex.Message}. Falling back to mouse input.", 10);
                            _warnedMagicInputFailed = true;
                        }

                        Settings.UseMagicInput.Value = false;
                        await TaskUtils.NextFrame();
                        continue;
                    }

                    didAttemptClick = true;
                    _sinceLastClick.Restart();
                    tryCount++;
                }
                else
                {
                    var position = label.GetClientRect().ClickRandomNum(5, 3) + GameController.Window.GetWindowRectangleTimeCache.TopLeft.ToVector2Num();
                    if (!IsTargeted(item, label))
                    {
                        await SetCursorPositionAsync(position, item, label);

                        // Some Delve chests don't consistently report targeted state.
                        // After a couple hover attempts, send a direct click fallback.
                        hoverAttemptsWithoutTarget++;
                        var canAttemptFallbackClick = tryCount == 0 || _sinceLastClick.ElapsedMilliseconds >= Settings.PauseBetweenClicks;
                        if (item.HasComponent<Chest>() && hoverAttemptsWithoutTarget >= 2 && canAttemptFallbackClick)
                        {
                            if (await CheckPortal(label)) return true;
                            EnsureLeftMouseUpIfNotPhysicallyHeld();
                            Input.Click(MouseButtons.Left);
                            didAttemptClick = true;
                            _sinceLastClick.Restart();
                            tryCount++;
                            hoverAttemptsWithoutTarget = 0;
                        }

                        await TaskUtils.NextFrame();
                        continue;
                    }

                    hoverAttemptsWithoutTarget = 0;

                    if (await CheckPortal(label)) return true;
                    if (!IsTargeted(item, label))
                    {
                        await TaskUtils.NextFrame();
                        continue;
                    }

                    var canAttemptNormalClick = tryCount == 0 || _sinceLastClick.ElapsedMilliseconds >= Settings.PauseBetweenClicks;
                    if (!canAttemptNormalClick)
                    {
                        await TaskUtils.NextFrame();
                        continue;
                    }

                    EnsureLeftMouseUpIfNotPhysicallyHeld();

                    Input.Click(MouseButtons.Left);
                    didAttemptClick = true;
                    _sinceLastClick.Restart();
                    tryCount++;
                }

                await TaskUtils.NextFrame();
            }
        }
        finally
        {
            if (inputBlocked)
            {
                EndBlockMouseInput();
            }

            EnsureLeftMouseUpIfNotPhysicallyHeld();

            if (restoreLeftMouseAfterPickup)
            {
                SetCursorPos(cursorSnapshot.X, cursorSnapshot.Y);
                _restoreHeldLeftMouseTill = DateTime.Now.AddMilliseconds(1200);
                _preserveLeftMouseIntentTill = DateTime.Now.AddMilliseconds(900);
                _forceRestoreLeftMouseTill = DateTime.Now.AddMilliseconds(1200);
                Input.LeftDown();
            }
            else if (inputBlocked)
            {
                _restoreHeldLeftMouseTill = DateTime.MinValue;
                SetCursorPos(cursorSnapshot.X, cursorSnapshot.Y);
            }
        }

        return didAttemptClick;
    }

    private async Task<bool> CheckPortal(Element label)
    {
        if (!IsPortalNearby(_portalLabel.Value, label)) return false;
        // in case of portal nearby do extra checks with delays
        if (IsPortalTargeted(_portalLabel.Value))
        {
            return true;
        }

        await Task.Delay(25);
        return IsPortalTargeted(_portalLabel.Value);
    }

    private static bool IsTargeted(Entity item, Element label)
    {
        if (item == null) return false;
        if (item.GetComponent<Targetable>()?.isTargeted is { } isTargeted)
        {
            return isTargeted;
        }

        return label is { HasShinyHighlight: true };
    }

    private static async SyncTask<bool> SetCursorPositionAsync(Vector2 position, Entity item, Element label)
    {
        Input.SetCursorPos(position);
        return await TaskUtils.CheckEveryFrame(() => IsTargeted(item, label), new CancellationTokenSource(20).Token);
    }
}
