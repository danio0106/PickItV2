using System;
using System.Linq;
using ExileCore.PoEMemory.Components;
using ExileCore.PoEMemory.MemoryObjects;
using SharpDX;
using ItemFilterLibrary;

namespace PickIt;

public partial class PickIt
{
    private bool CanFitInventory(ItemData groundItem)
    {
        if (_inventoryItems == null)
            return true; // Can't read inventory data yet — assume it fits and let the game decide.

        return FindSpotInventory(groundItem) != null;
    }

    private bool CanFitInventory(int itemHeight, int itemWidth)
    {
        if (_inventoryItems == null)
            return true;

        return FindSpotInventory(itemHeight, itemWidth) != null;
    }

        const int width = 12;
        const int height = 5;
    /// <summary>
    /// Finds a spot available in the inventory to place the item
    /// </summary>
    private Vector2? FindSpotInventory(ItemData item)
    {
        var inventoryItems = _inventoryItems?.InventorySlotItems;
        if (inventoryItems == null)
            return null;

        var itemToStackWith = inventoryItems.FirstOrDefault(x => CanItemBeStacked(item, x));
        if (itemToStackWith != null)
        {
            return new Vector2(itemToStackWith.PosX, itemToStackWith.PosY);
        }

        var itemHeight = item.Height;
        var itemWidth = item.Width;
        return FindSpotInventory(itemHeight, itemWidth);
    }

    private Vector2? FindSpotInventory(int itemHeight, int itemWidth)
    {
        var inventorySlots = _inventorySlotsWithItemIds.Value;
        if (inventorySlots == null)
        {
            return null;
        }

        for (var yCol = 0; yCol < height - (itemHeight - 1); yCol++)
        {
            for (var xRow = 0; xRow < width - (itemWidth - 1); xRow++)
            {
                var obstructed = false;

                for (var xWidth = 0; xWidth < itemWidth && !obstructed; xWidth++)
                for (var yHeight = 0; yHeight < itemHeight && !obstructed; yHeight++)
                {
                    obstructed |= inventorySlots[yCol + yHeight, xRow + xWidth] > 0;
                }

                if (!obstructed) return new Vector2(xRow, yCol);
            }
        }

        return null;
    }

    private static bool CanItemBeStacked(ItemData item, ServerInventory.InventSlotItem inventoryItem)
    {
        if (item.Entity.Path != inventoryItem.Item.Path)
            return false;

        if (!item.Entity.HasComponent<Stack>() || !inventoryItem.Item.HasComponent<Stack>())
            return false;

        var itemStackComp = item.Entity.GetComponent<Stack>();
        var inventoryItemStackComp = inventoryItem.Item.GetComponent<Stack>();

        /*
         * Reserved if the itemlevel is ever found as incubators dont have a mods comp?? why.
        if (item.BaseName.EndsWith(" Incubator") && inventoryItem.Item.HasComponent<Mods>())
        {
            return (item.ItemLevel == inventoryItem.Item.GetComponent<Mods>().ItemLevel) && inventoryItemStackComp.Size + itemStackComp.Size <= inventoryItemStackComp.Info.MaxStackSize;
        }
        */

        return inventoryItemStackComp.Size + itemStackComp.Size <= inventoryItemStackComp.Info.MaxStackSize;
    }

    private int[,] GetContainer2DArrayWithItemIds(ServerInventory containerItems)
    {
        if (containerItems == null)
            return null;

        var containerCells = new int[containerItems.Rows, containerItems.Columns];

        try
        {
            var itemId = 1;
            foreach (var item in containerItems.InventorySlotItems)
            {
                var itemSizeX = item.SizeX;
                var itemSizeY = item.SizeY;
                var inventPosX = item.PosX;
                var inventPosY = item.PosY;
                var startX = Math.Max(0, inventPosX);
                var startY = Math.Max(0, inventPosY);
                var endX = Math.Min(containerItems.Columns, inventPosX + itemSizeX);
                var endY = Math.Min(containerItems.Rows, inventPosY + itemSizeY);
                for (var y = startY; y < endY; y++)
                for (var x = startX; x < endX; x++)
                    containerCells[y, x] = itemId;
                itemId++;
            }
        }
        catch (Exception e)
        {
            // ignored
            LogMessage(e.ToString(), 5);
        }

        return containerCells;
    }
}