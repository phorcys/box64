#if !(defined(GO) && defined(GOM) && defined(GO2) && defined(DATA))
#error Meh...
#endif

GO(gtk_about_dialog_add_credit_section, vFppp)
GO(gtk_about_dialog_get_artists, pFp)
GO(gtk_about_dialog_get_authors, pFp)
GO(gtk_about_dialog_get_comments, pFp)
GO(gtk_about_dialog_get_copyright, pFp)
GO(gtk_about_dialog_get_documenters, pFp)
GO(gtk_about_dialog_get_license, pFp)
GO(gtk_about_dialog_get_license_type, uFp)
GO(gtk_about_dialog_get_logo, pFp)
GO(gtk_about_dialog_get_logo_icon_name, pFp)
GO(gtk_about_dialog_get_program_name, pFp)
GO(gtk_about_dialog_get_translator_credits, pFp)
GO(gtk_about_dialog_get_type, LFv)
GO(gtk_about_dialog_get_version, pFp)
GO(gtk_about_dialog_get_website, pFp)
GO(gtk_about_dialog_get_website_label, pFp)
GO(gtk_about_dialog_get_wrap_license, iFp)
GO(gtk_about_dialog_new, pFv)
GO(gtk_about_dialog_set_artists, vFpp)
GO(gtk_about_dialog_set_authors, vFpp)
GO(gtk_about_dialog_set_comments, vFpp)
GO(gtk_about_dialog_set_copyright, vFpp)
GO(gtk_about_dialog_set_documenters, vFpp)
//GO(gtk_about_dialog_set_email_hook, 
GO(gtk_about_dialog_set_license, vFpp)
GO(gtk_about_dialog_set_license_type, vFpu)
GO(gtk_about_dialog_set_logo, vFpp)
GO(gtk_about_dialog_set_logo_icon_name, vFpp)
GO(gtk_about_dialog_set_program_name, vFpp)
GO(gtk_about_dialog_set_translator_credits, vFpp)
//GO(gtk_about_dialog_set_url_hook, 
GO(gtk_about_dialog_set_version, vFpp)
GO(gtk_about_dialog_set_website, vFpp)
GO(gtk_about_dialog_set_website_label, vFpp)
GO(gtk_about_dialog_set_wrap_license, vFpi)
GO(gtk_accelerator_get_default_mod_mask, uFv)
GO(gtk_accelerator_get_label, pFuu)
GO(gtk_accelerator_name, pFuu)
GO(gtk_accelerator_parse, vFppp)
GO(gtk_accelerator_set_default_mod_mask, vFu)
GO(gtk_accelerator_valid, iFuu)
GO(gtk_accel_flags_get_type, LFv)
GO(gtk_accel_group_activate, iFpupuu)
GO(gtk_accel_group_connect, vFpuuup)  // Closure probably needs wrapping when not null
GO(gtk_accel_group_connect_by_path, vFppp)  // Closure probably needs wrapping when not null
GO(gtk_accel_group_disconnect, iFpp)    // Closure probably needs wrapping when not null
GO(gtk_accel_group_disconnect_key, iFpuu)
//GOM(gtk_accel_group_find, pFEppp)
GO(gtk_accel_group_from_accel_closure, pFp)
GO(gtk_accel_group_get_is_locked, iFp)  // Closure probably needs wrapping when not null
GO(gtk_accel_group_get_modifier_mask, uFp)
GO(gtk_accel_group_get_type, LFv)
GO(gtk_accel_group_lock, vFp)
GO(gtk_accel_group_new, pFv)
GO(gtk_accel_group_query, pFpuup)
GO(gtk_accel_groups_activate, iFpuu)
GO(gtk_accel_groups_from_object, pFp)
GO(gtk_accel_group_unlock, vFp)
GO(gtk_accel_label_get_accel_widget, pFp)
GO(gtk_accel_label_get_accel_width, uFp)
GO(gtk_accel_label_get_type, LFv)
GO(gtk_accel_label_new, pFp)
GO(gtk_accel_label_refetch, iFp)
//GOM(gtk_accel_label_set_accel_closure, vFpp)
GO(gtk_accel_label_set_accel_widget, vFpp)
GO(gtk_accel_map_add_entry, vFpuu)
GO(gtk_accel_map_add_filter, vFp)
GO(gtk_accel_map_change_entry, iFpuui)
//GOM(gtk_accel_map_foreach, vFpp)
//GOM(gtk_accel_map_foreach_unfiltered, vFpp)
GO(gtk_accel_map_get, pFv)
GO(gtk_accel_map_get_type, LFv)
GO(gtk_accel_map_load, vFp)
GO(gtk_accel_map_load_fd, vFi)
//GOM(gtk_accel_map_load_scanner, vFp)
GO(gtk_accel_map_lock_path, vFp)
GO(gtk_accel_map_lookup_entry, iFpp)
GO(gtk_accel_map_save, vFp)
GO(gtk_accel_map_save_fd, vFi)
GO(gtk_accel_map_unlock_path, vFp)
GO(gtk_accessible_connect_widget_destroyed, vFp)
GO(gtk_accessible_get_type, LFv)
GO(gtk_accessible_get_widget, pFp)
GO(gtk_accessible_set_widget, vFpp)
GO(gtk_actionable_get_type, LFv)
GO(gtk_action_activate, vFp)
GO(gtk_action_bar_get_type, LFv)
GO(gtk_action_block_activate, vFp)
//GO(gtk_action_block_activate_from, 
GO(gtk_action_connect_accelerator, vFp)
//GO(gtk_action_connect_proxy, 
GO(gtk_action_create_icon, pFpu)
GO(gtk_action_create_menu, pFp)
GO(gtk_action_create_menu_item, pFp)
GO(gtk_action_create_tool_item, pFp)
GO(gtk_action_disconnect_accelerator, vFp)
//GO(gtk_action_disconnect_proxy, 
//GOM(gtk_action_get_accel_closure, pFp)
GO(gtk_action_get_accel_path, pFp)
GO(gtk_action_get_always_show_image, iFp)
GO(gtk_action_get_gicon, pFp)
GO(gtk_action_get_icon_name, pFp)
GO(gtk_action_get_is_important, iFp)
GO(gtk_action_get_label, pFp)
GO(gtk_action_get_name, pFp)
GO(gtk_action_get_proxies, pFp)
GO(gtk_action_get_sensitive, iFp)
GO(gtk_action_get_short_label, pFp)
GO(gtk_action_get_stock_id, pFp)
GO(gtk_action_get_tooltip, pFp)
GO(gtk_action_get_type, LFv)
GO(gtk_action_get_visible, iFp)
GO(gtk_action_get_visible_horizontal, iFp)
GO(gtk_action_get_visible_vertical, iFp)
GO(gtk_action_group_add_action, vFpp)
//GOM(gtk_action_group_add_actions, vFppup)
//GOM(gtk_action_group_add_actions_full, vFppupp)
GO(gtk_action_group_add_action_with_accel, vFppp)
//GOM(gtk_action_group_add_radio_actions, vFppuipp)
//GOM(gtk_action_group_add_radio_actions_full, vFppuippp)
//GOM(gtk_action_group_add_toggle_actions, vFppup)
//GOM(gtk_action_group_add_toggle_actions_full, vFppupp)
GO(gtk_action_group_get_action, pFpp)
GO(gtk_action_group_get_name, pFp)
GO(gtk_action_group_get_sensitive, iFp)
GO(gtk_action_group_get_type, LFv)
GO(gtk_action_group_get_visible, iFp)
GO(gtk_action_group_list_actions, pFp)
GO(gtk_action_group_new, pFp)
GO(gtk_action_group_remove_action, vFpp)
GO(gtk_action_group_set_sensitive, vFpi)
//GOM(gtk_action_group_set_translate_func, vFpppp)
GO(gtk_action_group_set_translation_domain, vFpp)
GO(gtk_action_group_set_visible, vFpi)
GO(gtk_action_group_translate_string, pFpp)
GO(gtk_action_is_sensitive, iFp)
GO(gtk_action_is_visible, iFp)
GO(gtk_action_new, pFpppp)
GO(gtk_action_set_accel_group, vFpp)
GO(gtk_action_set_accel_path, vFpp)
GO(gtk_action_set_always_show_image, vFpi)
GO(gtk_action_set_gicon, vFpp)
GO(gtk_action_set_icon_name, vFpp)
GO(gtk_action_set_is_important, vFpi)
GO(gtk_action_set_label, vFpp)
GO(gtk_action_set_sensitive, vFpi)
GO(gtk_action_set_short_label, vFpp)
GO(gtk_action_set_stock_id, vFpp)
GO(gtk_action_set_tooltip, vFpp)
GO(gtk_action_set_visible, vFpi)
GO(gtk_action_set_visible_horizontal, vFpi)
GO(gtk_action_set_visible_vertical, vFpi)
GO(gtk_action_unblock_activate, vFp)
//GO(gtk_action_unblock_activate_from, 
GO(gtk_activatable_do_set_related_action, vFpp)
GO(gtk_activatable_get_related_action, pFp)
GO(gtk_activatable_get_type, LFv)
GO(gtk_activatable_get_use_action_appearance, iFp)
GO(gtk_activatable_set_related_action, vFpp)
GO(gtk_activatable_set_use_action_appearance, vFpi)
GO(gtk_activatable_sync_action_properties, vFpp)
GO(gtk_adjustment_changed, vFp)
GO(gtk_adjustment_clamp_page, vFpdd)
GO(gtk_adjustment_configure, vFpdddddd)
GO(gtk_adjustment_get_lower, dFp)
GO(gtk_adjustment_get_page_increment, dFp)
GO(gtk_adjustment_get_page_size, dFp)
GO(gtk_adjustment_get_step_increment, dFp)
GO(gtk_adjustment_get_type, LFv)
GO(gtk_adjustment_get_upper, dFp)
GO(gtk_adjustment_get_value, dFp)
GO(gtk_adjustment_new, pFdddddd)
GO(gtk_adjustment_set_lower, vFpd)
GO(gtk_adjustment_set_page_increment, vFpd)
GO(gtk_adjustment_set_page_size, vFpd)
GO(gtk_adjustment_set_step_increment, vFpd)
GO(gtk_adjustment_set_upper, vFpd)
GO(gtk_adjustment_set_value, vFpd)
GO(gtk_adjustment_value_changed, vFp)
GO(gtk_alignment_get_padding, vFppppp)
GO(gtk_alignment_get_type, LFv)
GO(gtk_alignment_new, pFffff)
GO(gtk_alignment_set, vFpffff)
GO(gtk_alignment_set_padding, vFpuuuu)
GO(gtk_align_get_type, LFv)
GO(gtk_alternative_dialog_button_order, iFp)
GO(gtk_anchor_type_get_type, LFv) // Warning: failed to confirm
GO(gtk_application_add_window, vFpp)
GO(gtk_application_get_new, pFpi) // Warning: failed to confirm
GO(gtk_application_get_type, LFv)
GO(gtk_application_new, pFpu)
GO(gtk_application_set_accels_for_action, vFppp)
GO(gtk_application_window_new, pFp)
GO(gtk_application_window_get_type, LFv)
GO(gtk_app_chooser_button_get_type, LFv)
GO(gtk_app_chooser_dialog_get_type, LFv)
GO(gtk_app_chooser_get_type, LFv)
GO(gtk_app_chooser_widget_get_type, LFv)
GO(gtk_arg_flags_get_type, LFv) // Warning: failed to confirm
GO(gtk_arrow_get_type, LFv)
GO(gtk_arrow_new, pFuu)
GO(gtk_arrow_placement_get_type, LFv)
GO(gtk_arrow_set, vFpuu)
GO(gtk_arrow_type_get_type, LFv)
GO(gtk_aspect_frame_get_type, LFv)
GO(gtk_aspect_frame_new, pFpfffi)
GO(gtk_aspect_frame_set, vFpfffi)
GO(gtk_assistant_add_action_widget, vFpp)
GO(gtk_assistant_append_page, iFpp)
GO(gtk_assistant_commit, vFp)
GO(gtk_assistant_get_current_page, iFp)
GO(gtk_assistant_get_n_pages, iFp)
GO(gtk_assistant_get_nth_page, pFpi)
GO(gtk_assistant_get_page_complete, iFpp)
GO(gtk_assistant_get_page_header_image, pFpp)
GO(gtk_assistant_get_page_side_image, pFpp)
GO(gtk_assistant_get_page_title, pFpp)
GO(gtk_assistant_get_page_type, uFpp)
GO(gtk_assistant_get_type, LFv)
GO(gtk_assistant_insert_page, iFppi)
GO(gtk_assistant_new, pFv)
GO(gtk_assistant_page_type_get_type, LFv)
GO(gtk_assistant_prepend_page, iFpp)
GO(gtk_assistant_remove_action_widget, vFpp)
GO(gtk_assistant_set_current_page, vFpi)
//GOM(gtk_assistant_set_forward_page_func, vFpppp)
GO(gtk_assistant_set_page_complete, vFppi)
GO(gtk_assistant_set_page_header_image, vFppp)
GO(gtk_assistant_set_page_side_image, vFppp)
GO(gtk_assistant_set_page_title, vFppp)
GO(gtk_assistant_set_page_type, vFppu)
GO(gtk_assistant_update_buttons_state, vFp)
GO(gtk_attach_options_get_type, LFv)
//GOM(gtk_binding_entry_add_signal, vFpuupuV)
GO(gtk_binding_entry_add_signall, vFpuupp)
//GO(gtk_binding_entry_clear, 
GO(gtk_binding_entry_remove, vFpuu)
GO(gtk_binding_entry_skip, vFpuu)
//GO(gtk_binding_parse_binding, 
GO(gtk_bindings_activate, iFpuu)
GO(gtk_bindings_activate_event, iFpp)
GO(gtk_binding_set_activate, iFpuup)
GO(gtk_binding_set_add_path, vFpupu)
GO(gtk_binding_set_by_class, pFp)
GO(gtk_binding_set_find, pFp)
GO(gtk_binding_set_new, pFp)
GO(gtk_bin_get_child, pFp)
GO(gtk_bin_get_type, LFv)
GO(gtk_border_copy, pFp)
GO(gtk_border_free, vFp)
GO(gtk_border_get_type, LFv)
GO(gtk_border_new, pFv)
GO(gtk_box_get_homogeneous, iFp)
GO(gtk_box_get_spacing, iFp)
GO(gtk_box_get_type, LFv)
GO(gtk_box_new, pFui)
GO(gtk_box_pack_end, vFppiiu)
GO(gtk_box_pack_end_defaults, vFpp) // Warning: failed to confirm
GO(gtk_box_pack_start, vFppiiu)
GO(gtk_box_pack_start_defaults, vFpp) // Warning: failed to confirm
GO(gtk_box_query_child_packing, vFpppppp)
GO(gtk_box_reorder_child, vFppi)
GO(gtk_box_set_child_packing, vFppiiuu)
GO(gtk_box_set_homogeneous, vFpi)
GO(gtk_box_set_spacing, vFpi)
GO(gtk_buildable_add_child, vFpppp)
GO(gtk_buildable_construct_child, pFppp)
GO(gtk_buildable_custom_finished, vFppppp)
GO(gtk_buildable_custom_tag_end, vFppppp)
GO(gtk_buildable_custom_tag_start, iFpppppp)    // Something to wrap?
GO(gtk_buildable_get_internal_child, pFppp)
GO(gtk_buildable_get_name, pFp)
GO(gtk_buildable_get_type, LFv)
GO(gtk_buildable_parser_finished, vFpp)
GO(gtk_buildable_set_buildable_property, vFpppp)
GO(gtk_buildable_set_name, vFpp)
GO(gtk_builder_add_from_file, uFppp)
GO(gtk_builder_add_from_resource, uFppp)
GO(gtk_builder_add_from_string, uFppLp)
GO(gtk_builder_add_objects_from_file, uFpppp)
GO(gtk_builder_add_objects_from_string, uFppLpp)
GOM(gtk_builder_connect_signals, vFEpp)
GOM(gtk_builder_connect_signals_full, vFEppp)
GO(gtk_builder_error_get_type, LFv)
GO(gtk_builder_error_quark, uFv)
GO(gtk_builder_get_object, pFpp)
GO(gtk_builder_get_objects, pFp)
GO(gtk_builder_get_translation_domain, pFp)
GO(gtk_builder_get_type, LFv)
GO(gtk_builder_get_type_from_name, LFpp)
GO(gtk_builder_new, pFv)
GO(gtk_builder_set_translation_domain, vFpp)
GO(gtk_builder_value_from_string, iFppppp)
GO(gtk_builder_value_from_string_type, iFpLppp)
GO(gtk_button_action_get_type, LFv) // Warning: failed to confirm
GO(gtk_button_box_get_child_ipadding, vFppp) // Warning: failed to confirm
GO(gtk_button_box_get_child_secondary, iFpp)
GO(gtk_button_box_get_child_size, vFppp) // Warning: failed to confirm
GO(gtk_button_box_get_layout, uFp)
GO(gtk_button_box_get_type, LFv)
GO(gtk_button_box_new, pFu)
GO(gtk_button_box_set_child_ipadding, vFpii) // Warning: failed to confirm
GO(gtk_button_box_set_child_secondary, vFppi)
GO(gtk_button_box_set_child_size, vFpii) // Warning: failed to confirm
GO(gtk_button_box_set_layout, vFpu)
GO(gtk_button_box_style_get_type, LFv)
GO(gtk_button_clicked, vFp)
GO(gtk_button_enter, vFp)
GO(gtk_button_get_alignment, vFppp)
GO(gtk_button_get_event_window, pFp)
GO(gtk_button_get_focus_on_click, iFp)
GO(gtk_button_get_image, pFp)
GO(gtk_button_get_image_position, uFp)
GO(gtk_button_get_label, pFp)
GO(gtk_button_get_relief, uFp)
GO(gtk_button_get_type, LFv)
GO(gtk_button_get_use_stock, iFp)
GO(gtk_button_get_use_underline, iFp)
GO(gtk_button_leave, vFp)
GO(gtk_button_new, pFv)
GO(gtk_button_new_from_stock, pFp)
GO(gtk_button_new_with_label, pFp)
GO(gtk_button_new_with_mnemonic, pFp)
GO(gtk_button_pressed, vFp)
GO(gtk_button_released, vFp)
GO(gtk_button_set_alignment, vFpff)
GO(gtk_button_set_always_show_image, vFpi)
GO(gtk_button_set_focus_on_click, vFpi)
GO(gtk_button_set_image, vFpp)
GO(gtk_button_set_image_position, vFpu)
GO(gtk_button_set_label, vFpp)
GO(gtk_button_set_relief, vFpu)
GO(gtk_button_set_use_stock, vFpi)
GO(gtk_button_set_use_underline, vFpi)
GO(gtk_buttons_type_get_type, LFv)
GO(gtk_cairo_should_draw_window, iFpp)
GO(gtk_calendar_clear_marks, vFp)
//GO(gtk_calendar_display_options, 
GO(gtk_calendar_display_options_get_type, LFv)
//GO(gtk_calendar_freeze, 
GO(gtk_calendar_get_date, vFpppp)
GO(gtk_calendar_get_detail_height_rows, iFp)
GO(gtk_calendar_get_detail_width_chars, iFp)
GO(gtk_calendar_get_display_options, uFp)
GO(gtk_calendar_get_type, LFv)
GO(gtk_calendar_mark_day, vFpu)
GO(gtk_calendar_new, pFv)
GO(gtk_calendar_select_day, vFpu)
GO(gtk_calendar_select_month, vFpuu)
//GOM(gtk_calendar_set_detail_func, vFpppp)
GO(gtk_calendar_set_detail_height_rows, vFpi)
GO(gtk_calendar_set_detail_width_chars, vFpi)
GO(gtk_calendar_set_display_options, vFpu)
//GO(gtk_calendar_thaw, 
GO(gtk_calendar_unmark_day, vFpu)
GO(gtk_cell_editable_editing_done, vFp)
GO(gtk_cell_editable_get_type, LFv)
GO(gtk_cell_editable_remove_widget, vFp)
GO(gtk_cell_editable_start_editing, vFpp)
GO(gtk_cell_layout_add_attribute, vFpppi)
GO(gtk_cell_layout_clear, vFp)
GO(gtk_cell_layout_clear_attributes, vFpp)
GO(gtk_cell_layout_get_cells, pFp)
GO(gtk_cell_layout_get_type, LFv)
GO(gtk_cell_layout_pack_end, vFppi)
GO(gtk_cell_layout_pack_start, vFppi)
GO(gtk_cell_layout_reorder, vFppi)
GO(gtk_cell_layout_set_attributes, vFpppppppppp)  // vaarg
//GOM(gtk_cell_layout_set_cell_data_func, vFEppppp)
GO(gtk_cell_renderer_accel_get_type, LFv)
GO(gtk_cell_renderer_accel_mode_get_type, LFv)
GO(gtk_cell_renderer_accel_new, pFv)
GO(gtk_cell_renderer_activate, iFppppppu)
GO(gtk_cell_renderer_combo_get_type, LFv)
GO(gtk_cell_renderer_combo_new, pFv)
//GO(gtk_cell_renderer_editing_canceled, 
GO(gtk_cell_renderer_get_alignment, vFppp)
GO(gtk_cell_renderer_get_fixed_size, vFppp)
GO(gtk_cell_renderer_get_padding, vFppp)
GO(gtk_cell_renderer_get_sensitive, iFp)
GO(gtk_cell_renderer_get_size, vFppppppp)
GO(gtk_cell_renderer_get_type, LFv)
GO(gtk_cell_renderer_get_visible, iFp)
GO(gtk_cell_renderer_mode_get_type, LFv)
GO(gtk_cell_renderer_pixbuf_get_type, LFv)
GO(gtk_cell_renderer_pixbuf_new, pFv)
GO(gtk_cell_renderer_progress_get_type, LFv)
GO(gtk_cell_renderer_progress_new, pFv)
GO(gtk_cell_renderer_render, vFpppppu)
GO(gtk_cell_renderer_set_alignment, vFpff)
GO(gtk_cell_renderer_set_fixed_size, vFpii)
GO(gtk_cell_renderer_set_padding, vFpii)
GO(gtk_cell_renderer_set_sensitive, vFpi)
GO(gtk_cell_renderer_set_visible, vFpi)
GO(gtk_cell_renderer_spin_get_type, LFv)
GO(gtk_cell_renderer_spinner_get_type, LFv)
GO(gtk_cell_renderer_spinner_new, pFv)
GO(gtk_cell_renderer_spin_new, pFv)
GO(gtk_cell_renderer_start_editing, pFppppppu)
GO(gtk_cell_renderer_state_get_type, LFv)
GO(gtk_cell_renderer_stop_editing, vFpi)
GO(gtk_cell_renderer_text_get_type, LFv)
GO(gtk_cell_renderer_text_new, pFv)
GO(gtk_cell_renderer_text_set_fixed_height_from_font, vFpi)
GO(gtk_cell_renderer_toggle_get_activatable, iFp)
GO(gtk_cell_renderer_toggle_get_active, iFp)
GO(gtk_cell_renderer_toggle_get_radio, iFp)
GO(gtk_cell_renderer_toggle_get_type, LFv)
GO(gtk_cell_renderer_toggle_new, pFv)
GO(gtk_cell_renderer_toggle_set_activatable, vFpi)
GO(gtk_cell_renderer_toggle_set_active, vFpi)
GO(gtk_cell_renderer_toggle_set_radio, vFpi)
GO(gtk_cell_type_get_type, LFv) // Warning: failed to confirm
//GO(gtk_cell_view_get_cell_renderers, 
GO(gtk_cell_view_get_displayed_row, pFp)
GO(gtk_cell_view_get_model, pFp)
GO(gtk_cell_view_get_size_of_row, iFppp)
GO(gtk_cell_view_get_type, LFv)
GO(gtk_cell_view_new, pFv)
GO(gtk_cell_view_new_with_markup, pFp)
GO(gtk_cell_view_new_with_pixbuf, pFp)
GO(gtk_cell_view_new_with_text, pFp)
GO(gtk_cell_view_set_background_color, vFpp)
GO(gtk_cell_view_set_displayed_row, vFpp)
GO(gtk_cell_view_set_model, vFpp)
GO(gtk_check_button_get_type, LFv)
GO(gtk_check_button_new, pFv)
GO(gtk_check_button_new_with_label, pFp)
GO(gtk_check_button_new_with_mnemonic, pFp)
GO(gtk_check_menu_item_get_active, iFp)
GO(gtk_check_menu_item_get_draw_as_radio, iFp)
GO(gtk_check_menu_item_get_inconsistent, iFp)
GO(gtk_check_menu_item_get_type, LFv)
GO(gtk_check_menu_item_new, pFv)
GO(gtk_check_menu_item_new_with_label, pFp)
GO(gtk_check_menu_item_new_with_mnemonic, pFp)
GO(gtk_check_menu_item_set_active, vFpi)
GO(gtk_check_menu_item_set_draw_as_radio, vFpi)
GO(gtk_check_menu_item_set_inconsistent, vFpi)
GO(gtk_check_menu_item_set_show_toggle, vFpi) // Warning: failed to confirm
GO(gtk_check_menu_item_toggled, vFp)
GO(gtk_check_version, pFuuu)
GO(gtk_clipboard_clear, vFp)
GO(gtk_clipboard_get, pFp)
GO(gtk_clipboard_get_default, pFp)
GO(gtk_clipboard_get_display, pFp)
GO(gtk_clipboard_get_for_display, pFpp)
GO(gtk_clipboard_get_owner, pFp)
GO(gtk_clipboard_get_type, LFv)
//GOM(gtk_clipboard_request_contents, vFEpppp)
//GOM(gtk_clipboard_request_image, vFEppp)
//GOM(gtk_clipboard_request_rich_text, vFEpppp)
//GOM(gtk_clipboard_request_targets, vFEppp)
GOM(gtk_clipboard_request_text, vFEppp)
//GOM(gtk_clipboard_request_uris, vFEppp)
GO(gtk_clipboard_set_can_store, vFppi)
GO(gtk_clipboard_set_image, vFpp)
GO(gtk_clipboard_set_text, vFppi)
GOM(gtk_clipboard_set_with_data, iFEppuppp)
GOM(gtk_clipboard_set_with_owner, iFEppuppp)
GO(gtk_clipboard_store, vFp)
GO(gtk_clipboard_wait_for_contents, pFpp)
GO(gtk_clipboard_wait_for_image, pFp)
GO(gtk_clipboard_wait_for_rich_text, pFpppp)
GO(gtk_clipboard_wait_for_targets, iFppp)
GO(gtk_clipboard_wait_for_text, pFp)
GO(gtk_clipboard_wait_for_uris, pFp)
GO(gtk_clipboard_wait_is_image_available, iFp)
GO(gtk_clipboard_wait_is_rich_text_available, iFpp)
GO(gtk_clipboard_wait_is_target_available, iFpp)
GO(gtk_clipboard_wait_is_text_available, iFp)
GO(gtk_clipboard_wait_is_uris_available, iFp)
GO(gtk_clist_append, iFpp) // Warning: failed to confirm
GO(gtk_clist_clear, vFp) // Warning: failed to confirm
GO(gtk_clist_columns_autosize, iFp) // Warning: failed to confirm
GO(gtk_clist_column_title_active, vFpi) // Warning: failed to confirm
GO(gtk_clist_column_title_passive, vFpi) // Warning: failed to confirm
GO(gtk_clist_column_titles_active, vFp) // Warning: failed to confirm
GO(gtk_clist_column_titles_hide, vFp) // Warning: failed to confirm
GO(gtk_clist_column_titles_passive, vFp) // Warning: failed to confirm
GO(gtk_clist_column_titles_show, vFp) // Warning: failed to confirm
GO(gtk_clist_drag_pos_get_type, LFv) // Warning: failed to confirm
GO(gtk_clist_find_row_from_data, iFpp) // Warning: failed to confirm
GO(gtk_clist_freeze, vFp) // Warning: failed to confirm
GO(gtk_clist_get_cell_style, pFpii) // Warning: failed to confirm
GO(gtk_clist_get_cell_type, iFpii) // Warning: failed to confirm
GO(gtk_clist_get_column_title, pFpi) // Warning: failed to confirm
GO(gtk_clist_get_column_widget, pFpi) // Warning: failed to confirm
GO(gtk_clist_get_hadjustment, pFp) // Warning: failed to confirm
GO(gtk_clist_get_pixmap, iFpiipp) // Warning: failed to confirm
GO(gtk_clist_get_pixtext, iFpiipppp) // Warning: failed to confirm
GO(gtk_clist_get_row_data, pFpi) // Warning: failed to confirm
GO(gtk_clist_get_row_style, pFpi) // Warning: failed to confirm
GO(gtk_clist_get_selectable, iFpi) // Warning: failed to confirm
GO(gtk_clist_get_selection_info, iFpiipp) // Warning: failed to confirm
GO(gtk_clist_get_text, iFpiip) // Warning: failed to confirm
GO(gtk_clist_get_type, LFv) // Warning: failed to confirm
GO(gtk_clist_get_vadjustment, pFp) // Warning: failed to confirm
GO(gtk_clist_insert, iFpip) // Warning: failed to confirm
GO(gtk_clist_moveto, vFpiiff) // Warning: failed to confirm
GO(gtk_clist_new, pFi) // Warning: failed to confirm
GO(gtk_clist_new_with_titles, pFip) // Warning: failed to confirm
GO(gtk_clist_optimal_column_width, iFpi) // Warning: failed to confirm
GO(gtk_clist_prepend, iFpp) // Warning: failed to confirm
GO(gtk_clist_remove, vFpi) // Warning: failed to confirm
GO(gtk_clist_row_is_visible, iFpi) // Warning: failed to confirm
GO(gtk_clist_row_move, vFpii) // Warning: failed to confirm
GO(gtk_clist_select_all, vFp) // Warning: failed to confirm
GO(gtk_clist_select_row, vFpii) // Warning: failed to confirm
GO(gtk_clist_set_auto_sort, vFpi) // Warning: failed to confirm
GO(gtk_clist_set_background, vFpip) // Warning: failed to confirm
GO(gtk_clist_set_button_actions, vFpiC) // Warning: failed to confirm
GO(gtk_clist_set_cell_style, vFpiip) // Warning: failed to confirm
GO(gtk_clist_set_column_auto_resize, iFpi) // Warning: failed to confirm
GO(gtk_clist_set_column_justification, vFpii) // Warning: failed to confirm
GO(gtk_clist_set_column_max_width, vFpii) // Warning: failed to confirm
GO(gtk_clist_set_column_min_width, vFpii) // Warning: failed to confirm
GO(gtk_clist_set_column_resizeable, vFpii) // Warning: failed to confirm
GO(gtk_clist_set_column_title, vFpip) // Warning: failed to confirm
GO(gtk_clist_set_column_visibility, vFpii) // Warning: failed to confirm
GO(gtk_clist_set_column_widget, vFpip) // Warning: failed to confirm
GO(gtk_clist_set_column_width, vFpii) // Warning: failed to confirm
//GOM(gtk_clist_set_compare_func, vFEpp)
GO(gtk_clist_set_foreground, vFpip) // Warning: failed to confirm
GO(gtk_clist_set_hadjustment, vFpp) // Warning: failed to confirm
GO(gtk_clist_set_pixmap, vFpiipp) // Warning: failed to confirm
GO(gtk_clist_set_pixtext, vFpiipCpp) // Warning: failed to confirm
GO(gtk_clist_set_reorderable, vFpi) // Warning: failed to confirm
GO(gtk_clist_set_row_data, vFpip) // Warning: failed to confirm
//GOM(gtk_clist_set_row_data_full, vFpipp)
GO(gtk_clist_set_row_height, vFpu) // Warning: failed to confirm
GO(gtk_clist_set_row_style, vFpip) // Warning: failed to confirm
GO(gtk_clist_set_selectable, vFpii) // Warning: failed to confirm
GO(gtk_clist_set_selection_mode, vFpi) // Warning: failed to confirm
GO(gtk_clist_set_shadow_type, vFpi) // Warning: failed to confirm
GO(gtk_clist_set_shift, vFpiiii) // Warning: failed to confirm
GO(gtk_clist_set_sort_column, vFpi) // Warning: failed to confirm
GO(gtk_clist_set_sort_type, vFpi) // Warning: failed to confirm
GO(gtk_clist_set_text, vFpiip) // Warning: failed to confirm
GO(gtk_clist_set_use_drag_icons, vFpi) // Warning: failed to confirm
GO(gtk_clist_set_vadjustment, vFpp) // Warning: failed to confirm
GO(gtk_clist_sort, vFp) // Warning: failed to confirm
GO(gtk_clist_swap_rows, vFpii) // Warning: failed to confirm
GO(gtk_clist_thaw, vFp) // Warning: failed to confirm
GO(gtk_clist_undo_selection, vFp) // Warning: failed to confirm
GO(gtk_clist_unselect_all, vFp) // Warning: failed to confirm
GO(gtk_clist_unselect_row, vFpii) // Warning: failed to confirm
GO(gtk_color_button_get_alpha, WFp)
GO(gtk_color_button_get_color, vFpp)
GO(gtk_color_button_get_title, pFp)
GO(gtk_color_button_get_type, LFv)
GO(gtk_color_button_get_use_alpha, iFp)
GO(gtk_color_button_new, pFv)
GO(gtk_color_button_new_with_color, pFp)
GO(gtk_color_button_new_with_rgba, pFp)
GO(gtk_color_button_set_alpha, vFpW)
GO(gtk_color_button_set_color, vFpp)
GO(gtk_color_button_set_rgba, vFpp)
GO(gtk_color_button_set_title, vFpp)
GO(gtk_color_button_set_use_alpha, vFpi)
GO(gtk_color_chooser_dialog_get_type, LFv)
GO(gtk_color_chooser_get_type, LFv)
GO(gtk_color_selection_dialog_get_color_selection, pFp)
GO(gtk_color_selection_dialog_get_type, LFv)
GO(gtk_color_selection_dialog_new, pFp)
GO(gtk_color_selection_get_color, vFpp) // Warning: failed to confirm
GO(gtk_color_selection_get_current_alpha, WFp)
GO(gtk_color_selection_get_current_color, vFpp)
GO(gtk_color_selection_get_has_opacity_control, iFp)
GO(gtk_color_selection_get_has_palette, iFp)
GO(gtk_color_selection_get_previous_alpha, WFp)
GO(gtk_color_selection_get_previous_color, vFpp)
GO(gtk_color_selection_get_type, LFv)
GO(gtk_color_selection_is_adjusting, iFp)
GO(gtk_color_selection_new, pFv)
GO(gtk_color_selection_palette_from_string, iFppp)
GO(gtk_color_selection_palette_to_string, pFpi)
//GOM(gtk_color_selection_set_change_palette_hook, pFEp)
//GOM(gtk_color_selection_set_change_palette_with_screen_hook, pFEp)
GO(gtk_color_selection_set_color, vFpp) // Warning: failed to confirm
GO(gtk_color_selection_set_current_alpha, vFpW)
GO(gtk_color_selection_set_current_color, vFpp)
GO(gtk_color_selection_set_has_opacity_control, vFpi)
GO(gtk_color_selection_set_has_palette, vFpi)
GO(gtk_color_selection_set_previous_alpha, vFpW)
GO(gtk_color_selection_set_previous_color, vFpp)
GO(gtk_color_selection_set_update_policy, vFpi) // Warning: failed to confirm
GO(gtk_combo_box_append_text, vFpp) // Warning: failed to confirm
GO(gtk_combo_box_entry_get_text_column, iFp) // Warning: failed to confirm
GO(gtk_combo_box_entry_get_type, LFv) // Warning: failed to confirm
GO(gtk_combo_box_entry_new, pFv) // Warning: failed to confirm
GO(gtk_combo_box_entry_new_text, pFv) // Warning: failed to confirm
GO(gtk_combo_box_entry_new_with_model, pFpi) // Warning: failed to confirm
GO(gtk_combo_box_entry_set_text_column, vFpi) // Warning: failed to confirm
GO(gtk_combo_box_get_active, iFp)
GO(gtk_combo_box_get_active_iter, iFpp)
GO(gtk_combo_box_get_active_text, pFp) // Warning: failed to confirm
GO(gtk_combo_box_get_add_tearoffs, iFp)
GO(gtk_combo_box_get_button_sensitivity, uFp)
GO(gtk_combo_box_get_column_span_column, iFp)
GO(gtk_combo_box_get_entry_text_column, iFp)
GO(gtk_combo_box_get_focus_on_click, iFp)
GO(gtk_combo_box_get_has_entry, iFp)
GO(gtk_combo_box_get_model, pFp)
GO(gtk_combo_box_get_popup_accessible, pFp)
//GOM(gtk_combo_box_get_row_separator_func, pFEp)
GO(gtk_combo_box_get_row_span_column, iFp)
GO(gtk_combo_box_get_title, pFp)
GO(gtk_combo_box_get_type, LFv)
GO(gtk_combo_box_get_wrap_width, iFp)
GO(gtk_combo_box_insert_text, vFpip) // Warning: failed to confirm
GO(gtk_combo_box_new, pFv)
GO(gtk_combo_box_new_text, pFv) // Warning: failed to confirm
GO(gtk_combo_box_new_with_entry, pFv)
GO(gtk_combo_box_new_with_model, pFp)
GO(gtk_combo_box_new_with_model_and_entry, pFp)
GO(gtk_combo_box_popdown, vFp)
GO(gtk_combo_box_popup, vFp)
GO(gtk_combo_box_prepend_text, vFpp) // Warning: failed to confirm
GO(gtk_combo_box_remove_text, vFpi) // Warning: failed to confirm
GO(gtk_combo_box_set_active, vFpi)
GO(gtk_combo_box_set_active_iter, vFpp)
GO(gtk_combo_box_set_add_tearoffs, vFpi)
GO(gtk_combo_box_set_button_sensitivity, vFpu)
GO(gtk_combo_box_set_column_span_column, vFpi)
GO(gtk_combo_box_set_entry_text_column, vFpi)
GO(gtk_combo_box_set_focus_on_click, vFpi)
GO(gtk_combo_box_set_model, vFpp)
//GOM(gtk_combo_box_set_row_separator_func, vFEpppp)
GO(gtk_combo_box_set_row_span_column, vFpi)
GO(gtk_combo_box_set_title, vFpp)
GO(gtk_combo_box_set_wrap_width, vFpi)
GO(gtk_combo_box_text_append, vFppp)
GO(gtk_combo_box_text_append_text, vFpp)
GO(gtk_combo_box_text_get_active_text, pFp)
GO(gtk_combo_box_text_get_type, LFv)
GO(gtk_combo_box_text_insert_text, vFpip)
GO(gtk_combo_box_text_new, pFv)
GO(gtk_combo_box_text_new_with_entry, pFv)
GO(gtk_combo_box_text_prepend_text, vFpp)
GO(gtk_combo_box_text_remove, vFpi)
GO(gtk_combo_box_text_remove_all, vFp)
GO(gtk_combo_disable_activate, vFp) // Warning: failed to confirm
GO(gtk_combo_get_type, LFv) // Warning: failed to confirm
GO(gtk_combo_new, pFv) // Warning: failed to confirm
GO(gtk_combo_set_case_sensitive, vFpi) // Warning: failed to confirm
GO(gtk_combo_set_item_string, vFppp) // Warning: failed to confirm
GO(gtk_combo_set_popdown_strings, vFpp) // Warning: failed to confirm
GO(gtk_combo_set_use_arrows, vFpi) // Warning: failed to confirm
GO(gtk_combo_set_use_arrows_always, vFpi) // Warning: failed to confirm
GO(gtk_combo_set_value_in_list, vFpii) // Warning: failed to confirm
GO(gtk_container_accessible_get_type, LFv) // Warning: failed to confirm
GO(gtk_container_add, vFpp)
GO(gtk_container_add_with_properties, vFpppppppppppp)    //vaarg
GO(gtk_container_check_resize, vFp)
//GOM(gtk_container_child_get, vFpppV)
GO(gtk_container_child_get_property, vFpppp)
//GOM(gtk_container_child_get_valist, vFpppA)
//GOM(gtk_container_child_set, vFpppV)
GO(gtk_container_child_set_property, vFpppp)
//GOM(gtk_container_child_set_valist, vFpppA)
GO(gtk_container_child_type, LFp)
GO(gtk_container_class_find_child_property, pFpp)   // Something to wrap?
GO(gtk_container_class_install_child_property, vFpup)
GO(gtk_container_class_list_child_properties, pFpp)
GOM(gtk_container_forall, vFEppp)
GOM(gtk_container_foreach, vFEppp)
//GOM(gtk_container_foreach_full, vFEppppp)
GO(gtk_container_get_border_width, uFp)
GO(gtk_container_get_children, pFp)
GO(gtk_container_get_focus_chain, iFpp)
GO(gtk_container_get_focus_child, pFp)
GO(gtk_container_get_focus_hadjustment, pFp)
GO(gtk_container_get_focus_vadjustment, pFp)
GO(gtk_container_get_resize_mode, uFp)
GO(gtk_container_get_type, LFv)
GO(gtk_container_propagate_expose, vFppp) // Warning: failed to confirm
GO(gtk_container_remove, vFpp)
GO(gtk_container_resize_children, vFp)
GO(gtk_container_set_border_width, vFpu)
GO(gtk_container_set_focus_chain, vFpp)
GO(gtk_container_set_focus_child, vFpp)
GO(gtk_container_set_focus_hadjustment, vFpp)
GO(gtk_container_set_focus_vadjustment, vFpp)
GO(gtk_container_set_reallocate_redraws, vFpi)
GO(gtk_container_set_resize_mode, vFpu)
GO(gtk_container_unset_focus_chain, vFp)
GO(gtk_corner_type_get_type, LFv)
GO(gtk_css_provider_get_default, pFv)
GO(gtk_css_provider_get_named, pFpp)
GO(gtk_css_provider_get_type, LFv)
GO(gtk_css_provider_load_from_data, iFpplp)
GO(gtk_css_provider_load_from_file, iFppp)
GO(gtk_css_provider_load_from_path, iFppp)
GO(gtk_css_provider_load_from_resource, vFpp)
GO(gtk_css_provider_new, pFv)
GO(gtk_css_provider_to_string, pFp)
GO(gtk_css_section_get_end_line, uFp)
GO(gtk_css_section_get_end_position, uFp)
GO(gtk_css_section_get_file, pFp)
GO(gtk_css_section_get_parent, pFp)
GO(gtk_css_section_get_section_type, uFp)
GO(gtk_css_section_get_start_line, uFp)
GO(gtk_css_section_get_start_position, uFp)
GO(gtk_css_section_ref, pFp)
GO(gtk_css_section_unref, vFp)
//GO(gtk_ctree_collapse, 
//GO(gtk_ctree_collapse_recursive, 
//GO(gtk_ctree_collapse_to_depth, 
//GO(gtk_ctree_expand, 
GO(gtk_ctree_expander_style_get_type, LFv) // Warning: failed to confirm
//GO(gtk_ctree_expand_recursive, 
//GO(gtk_ctree_expand_to_depth, 
GO(gtk_ctree_expansion_type_get_type, LFv) // Warning: failed to confirm
//GO(gtk_ctree_export_to_gnode, 
//GO(gtk_ctree_find, 
//GO(gtk_ctree_find_all_by_row_data, 
//GO(gtk_ctree_find_all_by_row_data_custom, 
//GO(gtk_ctree_find_by_row_data, 
//GO(gtk_ctree_find_by_row_data_custom, 
//GO(gtk_ctree_find_node_ptr, 
//GO(gtk_ctree_get_node_info, 
GO(gtk_ctree_get_type, LFv) // Warning: failed to confirm
//GO(gtk_ctree_insert_gnode, 
//GO(gtk_ctree_insert_node, 
//GO(gtk_ctree_is_ancestor, 
//GO(gtk_ctree_is_hot_spot, 
//GO(gtk_ctree_is_viewable, 
//GO(gtk_ctree_last, 
GO(gtk_ctree_line_style_get_type, LFv) // Warning: failed to confirm
//GO(gtk_ctree_move, 
//GO(gtk_ctree_new, 
//GO(gtk_ctree_new_with_titles, 
//GO(gtk_ctree_node_get_cell_style, 
//GO(gtk_ctree_node_get_cell_type, 
//GO(gtk_ctree_node_get_pixmap, 
//GO(gtk_ctree_node_get_pixtext, 
//GO(gtk_ctree_node_get_row_data, 
//GO(gtk_ctree_node_get_row_style, 
//GO(gtk_ctree_node_get_selectable, 
//GO(gtk_ctree_node_get_text, 
GO(gtk_ctree_node_get_type, LFv) // Warning: failed to confirm
//GO(gtk_ctree_node_is_visible, 
//GO(gtk_ctree_node_moveto, 
//GO(gtk_ctree_node_nth, 
//GO(gtk_ctree_node_set_background, 
//GO(gtk_ctree_node_set_cell_style, 
//GO(gtk_ctree_node_set_foreground, 
//GO(gtk_ctree_node_set_pixmap, 
//GO(gtk_ctree_node_set_pixtext, 
//GO(gtk_ctree_node_set_row_data, 
//GO(gtk_ctree_node_set_row_data_full, 
//GO(gtk_ctree_node_set_row_style, 
//GO(gtk_ctree_node_set_selectable, 
//GO(gtk_ctree_node_set_shift, 
//GO(gtk_ctree_node_set_text, 
GO(gtk_ctree_pos_get_type, LFv) // Warning: failed to confirm
//GO(gtk_ctree_post_recursive, 
//GO(gtk_ctree_post_recursive_to_depth, 
//GO(gtk_ctree_pre_recursive, 
//GO(gtk_ctree_pre_recursive_to_depth, 
//GO(gtk_ctree_real_select_recursive, 
//GO(gtk_ctree_remove_node, 
//GO(gtk_ctree_select, 
//GO(gtk_ctree_select_recursive, 
//GO(gtk_ctree_set_drag_compare_func, 
//GO(gtk_ctree_set_expander_style, 
//GO(gtk_ctree_set_indent, 
//GO(gtk_ctree_set_line_style, 
//GO(gtk_ctree_set_node_info, 
//GO(gtk_ctree_set_show_stub, 
//GO(gtk_ctree_set_spacing, 
//GO(gtk_ctree_sort_node, 
//GO(gtk_ctree_sort_recursive, 
//GO(gtk_ctree_toggle_expansion, 
//GO(gtk_ctree_toggle_expansion_recursive, 
//GO(gtk_ctree_unselect, 
//GO(gtk_ctree_unselect_recursive, 
GO(gtk_curve_get_type, LFv) // Warning: failed to confirm
GO(gtk_curve_get_vector, vFpip) // Warning: failed to confirm
GO(gtk_curve_new, pFv) // Warning: failed to confirm
GO(gtk_curve_reset, vFp) // Warning: failed to confirm
GO(gtk_curve_set_curve_type, vFpi) // Warning: failed to confirm
GO(gtk_curve_set_gamma, vFpf) // Warning: failed to confirm
GO(gtk_curve_set_range, vFpffff) // Warning: failed to confirm
GO(gtk_curve_set_vector, vFpip) // Warning: failed to confirm
GO(gtk_curve_type_get_type, LFv) // Warning: failed to confirm
GO(gtk_custom_paper_unix_dialog_get_type, LFv) // Warning: failed to confirm
GO(gtk_debug_flag_get_type, LFv)
GO(gtk_decorated_window_calculate_frame_size, vFp) // Warning: failed to confirm
GO(gtk_decorated_window_init, vFp) // Warning: failed to confirm
GO(gtk_decorated_window_move_resize_window, vFpiiii) // Warning: failed to confirm
GO(gtk_decorated_window_set_title, vFpp) // Warning: failed to confirm
GO(gtk_delete_type_get_type, LFv)
GO(gtk_dest_defaults_get_type, LFv)
GO(gtk_dialog_add_action_widget, vFppi)
GO(gtk_dialog_add_button, pFppi)
GOM(gtk_dialog_add_buttons, vFEppV)
GO(gtk_dialog_flags_get_type, LFv)
GO(gtk_dialog_get_action_area, pFp)
GO(gtk_dialog_get_content_area, pFp)
GO(gtk_dialog_get_has_separator, iFp) // Warning: failed to confirm
GO(gtk_dialog_get_response_for_widget, iFpp)
GO(gtk_dialog_get_type, LFv)
GO(gtk_dialog_get_widget_for_response, pFpi)
GO(gtk_dialog_new, pFv)
GO(gtk_dialog_new_with_buttons, pFppipppppppppppp)    //vaarg
GO(gtk_dialog_response, vFpi)
GO(gtk_dialog_run, iFp)
GO(gtk_dialog_set_alternative_button_order, vFpiiiiiiiiiiiiiiiiii)  // vaarg, should wrap using gtk_dialog_set_alternative_button_order_from_array
GO(gtk_dialog_set_alternative_button_order_from_array, vFpip)
GO(gtk_dialog_set_default_response, vFpi)
GO(gtk_dialog_set_has_separator, vFpi) // Warning: failed to confirm
GO(gtk_dialog_set_response_sensitive, vFpii)
GO(gtk_direction_type_get_type, LFv)
GO(gtk_disable_setlocale, vFv)
GO(gtk_distribute_natural_allocation, iFiup)
GO(gtk_drag_begin, pFppuip)
GO(gtk_drag_check_threshold, iFpiiii)
GO(gtk_drag_dest_add_image_targets, vFp)
GO(gtk_drag_dest_add_text_targets, vFp)
GO(gtk_drag_dest_add_uri_targets, vFp)
GO(gtk_drag_dest_find_target, pFppp)
GO(gtk_drag_dest_get_target_list, pFp)
GO(gtk_drag_dest_get_track_motion, iFp)
GO(gtk_drag_dest_set, vFpupiu)
GO(gtk_drag_dest_set_proxy, vFppui)
GO(gtk_drag_dest_set_target_list, vFpp)
GO(gtk_drag_dest_set_track_motion, vFpi)
GO(gtk_drag_dest_unset, vFp)
GO(gtk_drag_finish, vFpiiu)
GO(gtk_drag_get_data, vFpppu)
GO(gtk_drag_get_source_widget, pFp)
GO(gtk_drag_highlight, vFp)
GO(gtk_drag_result_get_type, LFv)
GO(gtk_drag_set_default_icon, vFpppii) // Warning: failed to confirm
GO(gtk_drag_set_icon_default, vFp)
GO(gtk_drag_set_icon_name, vFppii)
GO(gtk_drag_set_icon_pixbuf, vFppii)
GO(gtk_drag_set_icon_pixmap, vFppppii) // Warning: failed to confirm
GO(gtk_drag_set_icon_stock, vFppii)
GO(gtk_drag_set_icon_widget, vFppii)
GO(gtk_drag_source_add_image_targets, vFp)
GO(gtk_drag_source_add_text_targets, vFp)
GO(gtk_drag_source_add_uri_targets, vFp)
GO(gtk_drag_source_get_target_list, pFp)
GO(gtk_drag_source_set, vFpupiu)
GO(gtk_drag_source_set_icon, vFpppp) // Warning: failed to confirm
GO(gtk_drag_source_set_icon_name, vFpp)
GO(gtk_drag_source_set_icon_pixbuf, vFpp)
GO(gtk_drag_source_set_icon_stock, vFpp)
GO(gtk_drag_source_set_target_list, vFpp)
GO(gtk_drag_source_unset, vFp)
GO(gtk_drag_unhighlight, vFp)
GO(gtk_draw_arrow, vFppiiiiiiii) // Warning: failed to confirm
GO(gtk_draw_box, vFppiiiiii) // Warning: failed to confirm
GO(gtk_draw_box_gap, vFppiiiiiiiii) // Warning: failed to confirm
GO(gtk_draw_check, vFppiiiiii) // Warning: failed to confirm
GO(gtk_draw_diamond, vFppiiiiii) // Warning: failed to confirm
GO(gtk_draw_expander, vFppiiii) // Warning: failed to confirm
GO(gtk_draw_extension, vFppiiiiiii) // Warning: failed to confirm
GO(gtk_draw_flat_box, vFppiiiiii) // Warning: failed to confirm
GO(gtk_draw_focus, vFppiiii) // Warning: failed to confirm
GO(gtk_draw_handle, vFppiiiiiii) // Warning: failed to confirm
GO(gtk_draw_hline, vFppiiii) // Warning: failed to confirm
GO(gtk_drawing_area_get_type, LFv)
GO(gtk_drawing_area_new, pFv)
GO(gtk_drawing_area_size, vFpii) // Warning: failed to confirm
GO(gtk_draw_insertion_cursor, vFpppiui)
GO(gtk_draw_layout, vFppiiiip) // Warning: failed to confirm
GO(gtk_draw_option, vFppiiiiii) // Warning: failed to confirm
GO(gtk_draw_polygon, vFppiipii) // Warning: failed to confirm
GO(gtk_draw_resize_grip, vFppiiiiii) // Warning: failed to confirm
GO(gtk_draw_shadow, vFppiiiiii) // Warning: failed to confirm
GO(gtk_draw_shadow_gap, vFppiiiiiiiii) // Warning: failed to confirm
GO(gtk_draw_slider, vFppiiiiiii) // Warning: failed to confirm
GO(gtk_draw_string, vFppiiip) // Warning: failed to confirm
GO(gtk_draw_tab, vFppiiiiii) // Warning: failed to confirm
GO(gtk_draw_vline, vFppiiii) // Warning: failed to confirm
GO(gtk_editable_copy_clipboard, vFp)
GO(gtk_editable_cut_clipboard, vFp)
GO(gtk_editable_delete_selection, vFp)
GO(gtk_editable_delete_text, vFpii)
GO(gtk_editable_get_chars, pFpii)
GO(gtk_editable_get_editable, iFp)
GO(gtk_editable_get_position, iFp)
GO(gtk_editable_get_selection_bounds, iFppp)
GO(gtk_editable_get_type, LFv)
GO(gtk_editable_insert_text, vFppip)
GO(gtk_editable_paste_clipboard, vFp)
GO(gtk_editable_select_region, vFpii)
GO(gtk_editable_set_editable, vFpi)
GO(gtk_editable_set_position, vFpi)
GO(gtk_entry_append_text, vFpp) // Warning: failed to confirm
GO(gtk_entry_buffer_delete_text, uFpui)
GO(gtk_entry_buffer_emit_deleted_text, vFpuu)
GO(gtk_entry_buffer_emit_inserted_text, vFpupu)
GO(gtk_entry_buffer_get_bytes, LFp)
GO(gtk_entry_buffer_get_length, uFp)
GO(gtk_entry_buffer_get_max_length, iFp)
GO(gtk_entry_buffer_get_text, pFp)
GO(gtk_entry_buffer_get_type, LFv)
GO(gtk_entry_buffer_insert_text, uFpupi)
GO(gtk_entry_buffer_new, pFpi)
GO(gtk_entry_buffer_set_max_length, vFpi)
GO(gtk_entry_buffer_set_text, vFppi)
GO(gtk_entry_completion_complete, vFp)
GO(gtk_entry_completion_delete_action, vFpi)
GO(gtk_entry_completion_get_completion_prefix, pFp)
GO(gtk_entry_completion_get_entry, pFp)
GO(gtk_entry_completion_get_inline_completion, iFp)
GO(gtk_entry_completion_get_inline_selection, iFp)
GO(gtk_entry_completion_get_minimum_key_length, iFp)
GO(gtk_entry_completion_get_model, pFp)
GO(gtk_entry_completion_get_popup_completion, iFp)
GO(gtk_entry_completion_get_popup_set_width, iFp)
GO(gtk_entry_completion_get_popup_single_match, iFp)
GO(gtk_entry_completion_get_text_column, iFp)
GO(gtk_entry_completion_get_type, LFv)
GO(gtk_entry_completion_insert_action_markup, vFpip)
GO(gtk_entry_completion_insert_action_text, vFpip)
GO(gtk_entry_completion_insert_prefix, vFp)
GO(gtk_entry_completion_new, pFv)
GO(gtk_entry_completion_set_inline_completion, vFpi)
GO(gtk_entry_completion_set_inline_selection, vFpi)
//GOM(gtk_entry_completion_set_match_func, vFpppp)
GO(gtk_entry_completion_set_minimum_key_length, vFpi)
GO(gtk_entry_completion_set_model, vFpp)
GO(gtk_entry_completion_set_popup_completion, vFpi)
GO(gtk_entry_completion_set_popup_set_width, vFpi)
GO(gtk_entry_completion_set_popup_single_match, vFpi)
GO(gtk_entry_completion_set_text_column, vFpi)
GO(gtk_entry_get_activates_default, iFp)
GO(gtk_entry_get_alignment, fFp)
GO(gtk_entry_get_buffer, pFp)
GO(gtk_entry_get_completion, pFp)
GO(gtk_entry_get_current_icon_drag_source, iFp)
GO(gtk_entry_get_cursor_hadjustment, pFp)
GO(gtk_entry_get_has_frame, iFp)
GO(gtk_entry_get_icon_activatable, iFpu)
GO(gtk_entry_get_icon_at_pos, iFpii)
GO(gtk_entry_get_icon_gicon, pFpu)
GO(gtk_entry_get_icon_name, pFpu)
GO(gtk_entry_get_icon_pixbuf, pFpu)
GO(gtk_entry_get_icon_sensitive, iFpu)
GO(gtk_entry_get_icon_stock, pFpu)
GO(gtk_entry_get_icon_storage_type, uFpu)
GO(gtk_entry_get_icon_tooltip_markup, pFpu)
GO(gtk_entry_get_icon_tooltip_text, pFpu)
//GO(gtk_entry_get_icon_window, 
GO(gtk_entry_get_inner_border, pFp)
GO(gtk_entry_get_invisible_char, uFp)
GO(gtk_entry_get_layout, pFp)
GO(gtk_entry_get_layout_offsets, vFppp)
GO(gtk_entry_get_max_length, iFp)
GO(gtk_entry_get_overwrite_mode, iFp)
GO(gtk_entry_get_progress_fraction, dFp)
GO(gtk_entry_get_progress_pulse_step, dFp)
GO(gtk_entry_get_text, pFp)
GO(gtk_entry_get_text_length, WFp)
//GO(gtk_entry_get_text_window, 
GO(gtk_entry_get_type, LFv)
GO(gtk_entry_get_visibility, iFp)
GO(gtk_entry_get_width_chars, iFp)
GO(gtk_entry_icon_position_get_type, LFv)
GO(gtk_entry_im_context_filter_keypress, iFpp)
GO(gtk_entry_layout_index_to_text_index, iFpi)
GO(gtk_entry_new, pFv)
GO(gtk_entry_new_with_buffer, pFp)
GO(gtk_entry_new_with_max_length, pFi) // Warning: failed to confirm
GO(gtk_entry_prepend_text, vFpp) // Warning: failed to confirm
GO(gtk_entry_progress_pulse, vFp)
GO(gtk_entry_reset_im_context, vFp)
GO(gtk_entry_select_region, vFpii) // Warning: failed to confirm
GO(gtk_entry_set_activates_default, vFpi)
GO(gtk_entry_set_alignment, vFpf)
GO(gtk_entry_set_buffer, vFpp)
GO(gtk_entry_set_completion, vFpp)
GO(gtk_entry_set_cursor_hadjustment, vFpp)
GO(gtk_entry_set_editable, vFpi) // Warning: failed to confirm
GO(gtk_entry_set_has_frame, vFpi)
GO(gtk_entry_set_icon_activatable, vFpui)
GO(gtk_entry_set_icon_drag_source, vFpupu)
GO(gtk_entry_set_icon_from_gicon, vFpup)
GO(gtk_entry_set_icon_from_icon_name, vFpup)
GO(gtk_entry_set_icon_from_pixbuf, vFpup)
GO(gtk_entry_set_icon_from_stock, vFpup)
GO(gtk_entry_set_icon_sensitive, vFpui)
GO(gtk_entry_set_icon_tooltip_markup, vFpup)
GO(gtk_entry_set_icon_tooltip_text, vFpup)
GO(gtk_entry_set_inner_border, vFpp)
GO(gtk_entry_set_invisible_char, vFpu)
GO(gtk_entry_set_max_length, vFpi)
GO(gtk_entry_set_overwrite_mode, vFpi)
GO(gtk_entry_set_position, vFpi) // Warning: failed to confirm
GO(gtk_entry_set_progress_fraction, vFpd)
GO(gtk_entry_set_progress_pulse_step, vFpd)
GO(gtk_entry_set_text, vFpp)
GO(gtk_entry_set_visibility, vFpi)
GO(gtk_entry_set_width_chars, vFpi)
GO(gtk_entry_text_index_to_layout_index, iFpi)
GO(gtk_entry_unset_invisible_char, vFp)
GOM(gtk_enumerate_printers, vFEpppi) // Warning: failed to confirm
GO(gtk_event_box_get_above_child, iFp)
GO(gtk_event_box_get_type, LFv)
GO(gtk_event_box_get_visible_window, iFp)
GO(gtk_event_box_new, pFv)
GO(gtk_event_box_set_above_child, vFpi)
GO(gtk_event_box_set_visible_window, vFpi)
GO(gtk_event_controller_set_propagation_phase, vFpu)
GO(gtk_events_pending, iFv)
GO(gtk_exit, vFi) // Warning: failed to confirm
GO(gtk_expander_get_expanded, iFp)
GO(gtk_expander_get_label, pFp)
GO(gtk_expander_get_label_fill, iFp)
GO(gtk_expander_get_label_widget, pFp)
GO(gtk_expander_get_spacing, iFp)
GO(gtk_expander_get_type, LFv)
GO(gtk_expander_get_use_markup, iFp)
GO(gtk_expander_get_use_underline, iFp)
GO(gtk_expander_new, pFp)
GO(gtk_expander_new_with_mnemonic, pFp)
GO(gtk_expander_set_expanded, vFpi)
GO(gtk_expander_set_label, vFpp)
GO(gtk_expander_set_label_fill, vFpi)
GO(gtk_expander_set_label_widget, vFpp)
GO(gtk_expander_set_spacing, vFpi)
GO(gtk_expander_set_use_markup, vFpi)
GO(gtk_expander_set_use_underline, vFpi)
GO(gtk_expander_style_get_type, LFv)
GO(gtk_false, iFv)
GO(gtk_file_chooser_action_get_type, LFv)
GO(gtk_file_chooser_add_filter, vFpp)
GO(gtk_file_chooser_add_shortcut_folder, iFppp)
GO(gtk_file_chooser_add_shortcut_folder_uri, iFppp)
GO(gtk_file_chooser_button_get_focus_on_click, iFp)
GO(gtk_file_chooser_button_get_title, pFp)
GO(gtk_file_chooser_button_get_type, LFv)
GO(gtk_file_chooser_button_get_width_chars, iFp)
GO(gtk_file_chooser_button_new, pFpu)
GO(gtk_file_chooser_button_new_with_backend, pFpip) // Warning: failed to confirm
GO(gtk_file_chooser_button_new_with_dialog, pFp)
GO(gtk_file_chooser_button_set_focus_on_click, vFpi)
GO(gtk_file_chooser_button_set_title, vFpp)
GO(gtk_file_chooser_button_set_width_chars, vFpi)
GO(gtk_file_chooser_confirmation_get_type, LFv)
GO(gtk_file_chooser_dialog_get_type, LFv)
GO(gtk_file_chooser_dialog_new, pFppipipipipipipip)  // vaargs (so pFppipV) with additionnal buttons, end with a NULL
GO(gtk_file_chooser_dialog_new_with_backend, pFppippipipipipipip)   // same but pFppippV
GO(gtk_file_chooser_error_get_type, LFv)
GO(gtk_file_chooser_error_quark, uFv)
GO(gtk_file_chooser_get_action, uFp)
GO(gtk_file_chooser_get_create_folders, iFp)
GO(gtk_file_chooser_get_current_folder, pFp)
GO(gtk_file_chooser_get_current_folder_file, pFp)
GO(gtk_file_chooser_get_current_folder_uri, pFp)
GO(gtk_file_chooser_get_do_overwrite_confirmation, iFp)
GO(gtk_file_chooser_get_extra_widget, pFp)
GO(gtk_file_chooser_get_file, pFp)
GO(gtk_file_chooser_get_filename, pFp)
GO(gtk_file_chooser_get_filenames, pFp)
GO(gtk_file_chooser_get_files, pFp)
GO(gtk_file_chooser_get_filter, pFp)
GO(gtk_file_chooser_get_filters, pFp) // Warning: failed to confirm
GO(gtk_file_chooser_get_local_only, iFp)
GO(gtk_file_chooser_get_preview_file, pFp)
GO(gtk_file_chooser_get_preview_filename, pFp)
GO(gtk_file_chooser_get_preview_uri, pFp)
GO(gtk_file_chooser_get_preview_widget, pFp)
GO(gtk_file_chooser_get_preview_widget_active, iFp)
GO(gtk_file_chooser_get_select_multiple, iFp)
GO(gtk_file_chooser_get_show_hidden, iFp)
GO(gtk_file_chooser_get_type, LFv)
GO(gtk_file_chooser_get_uri, pFp)
GO(gtk_file_chooser_get_uris, pFp)
GO(gtk_file_chooser_get_use_preview_label, iFp)
GO(gtk_file_chooser_list_filters, pFp)
GO(gtk_file_chooser_list_shortcut_folders, pFp)
GO(gtk_file_chooser_list_shortcut_folder_uris, pFp)
GO(gtk_file_chooser_native_new, pFppupp)
GO(gtk_file_chooser_remove_filter, vFpp)
GO(gtk_file_chooser_remove_shortcut_folder, iFppp)
GO(gtk_file_chooser_remove_shortcut_folder_uri, iFppp)
GO(gtk_file_chooser_select_all, vFp)
GO(gtk_file_chooser_select_file, iFppp)
GO(gtk_file_chooser_select_filename, iFpp)
GO(gtk_file_chooser_select_uri, iFpp)
GO(gtk_file_chooser_set_action, vFpu)
GO(gtk_file_chooser_set_create_folders, vFpi)
GO(gtk_file_chooser_set_current_folder, iFpp)
GO(gtk_file_chooser_set_current_folder_file, iFppp)
GO(gtk_file_chooser_set_current_folder_uri, iFpp)
GO(gtk_file_chooser_set_current_name, vFpp)
GO(gtk_file_chooser_set_do_overwrite_confirmation, vFpi)
GO(gtk_file_chooser_set_extra_widget, vFpp)
GO(gtk_file_chooser_set_file, iFppp)
GO(gtk_file_chooser_set_filename, iFpp)
GO(gtk_file_chooser_set_filter, vFpp)
GO(gtk_file_chooser_set_local_only, vFpi)
GO(gtk_file_chooser_set_preview_widget, vFpp)
GO(gtk_file_chooser_set_preview_widget_active, vFpi)
GO(gtk_file_chooser_set_select_multiple, vFpi)
GO(gtk_file_chooser_set_show_hidden, vFpi)
GO(gtk_file_chooser_set_uri, iFpp)
GO(gtk_file_chooser_set_use_preview_label, vFpi)
GO(gtk_file_chooser_unselect_all, vFp)
GO(gtk_file_chooser_unselect_file, vFpp)
GO(gtk_file_chooser_unselect_filename, vFpp)
GO(gtk_file_chooser_unselect_uri, vFpp)
GO(gtk_file_chooser_widget_get_type, LFv)
GO(gtk_file_chooser_widget_new, pFu)
GO(gtk_file_chooser_widget_new_with_backend, pFip) // Warning: failed to confirm
GOM(gtk_file_filter_add_custom, vFEpuppp)
GO(gtk_file_filter_add_mime_type, vFpp)
GO(gtk_file_filter_add_pattern, vFpp)
GO(gtk_file_filter_add_pixbuf_formats, vFp)
GO(gtk_file_filter_filter, iFpp)
GO(gtk_file_filter_flags_get_type, LFv)
GO(gtk_file_filter_get_name, pFp)
GO(gtk_file_filter_get_needed, uFp)
GO(gtk_file_filter_get_type, LFv)
GO(gtk_file_filter_new, pFv)
GO(gtk_file_filter_set_name, vFpp)
GO(gtk_file_selection_complete, vFpp) // Warning: failed to confirm
GO(gtk_file_selection_get_filename, pFp) // Warning: failed to confirm
GO(gtk_file_selection_get_selections, pFp) // Warning: failed to confirm
GO(gtk_file_selection_get_select_multiple, iFp) // Warning: failed to confirm
GO(gtk_file_selection_get_type, LFv) // Warning: failed to confirm
GO(gtk_file_selection_hide_fileop_buttons, vFp) // Warning: failed to confirm
GO(gtk_file_selection_new, pFp) // Warning: failed to confirm
GO(gtk_file_selection_set_filename, vFpp) // Warning: failed to confirm
GO(gtk_file_selection_set_select_multiple, vFpi) // Warning: failed to confirm
GO(gtk_file_selection_show_fileop_buttons, vFp) // Warning: failed to confirm
GO(gtk_fixed_get_has_window, iFp) // Warning: failed to confirm
GO(gtk_fixed_get_type, LFv)
GO(gtk_fixed_move, vFppii)
GO(gtk_fixed_new, pFv)
GO(gtk_fixed_put, vFppii)
GO(gtk_fixed_set_has_window, vFpi) // Warning: failed to confirm
GO(gtk_flow_box_child_get_type, LFv)
GO(gtk_flow_box_get_type, LFv)
GO(gtk_font_button_get_font_name, pFp)
GO(gtk_font_button_get_show_size, iFp)
GO(gtk_font_button_get_show_style, iFp)
GO(gtk_font_button_get_title, pFp)
GO(gtk_font_button_get_type, LFv)
GO(gtk_font_button_get_use_font, iFp)
GO(gtk_font_button_get_use_size, iFp)
GO(gtk_font_button_new, pFv)
GO(gtk_font_button_new_with_font, pFp)
GO(gtk_font_button_set_font_name, iFpp)
GO(gtk_font_button_set_show_size, vFpi)
GO(gtk_font_button_set_show_style, vFpi)
GO(gtk_font_button_set_title, vFpp)
GO(gtk_font_button_set_use_font, vFpi)
GO(gtk_font_button_set_use_size, vFpi)
GO(gtk_font_chooser_get_type, LFv)
GO(gtk_font_selection_dialog_get_apply_button, pFp) // Warning: failed to confirm
GO(gtk_font_selection_dialog_get_cancel_button, pFp)
GO(gtk_font_selection_dialog_get_font, pFp) // Warning: failed to confirm
GO(gtk_font_selection_dialog_get_font_name, pFp)
GO(gtk_font_selection_dialog_get_font_selection, pFp)
GO(gtk_font_selection_dialog_get_ok_button, pFp)
GO(gtk_font_selection_dialog_get_preview_text, pFp)
GO(gtk_font_selection_dialog_get_type, LFv)
GO(gtk_font_selection_dialog_new, pFp)
GO(gtk_font_selection_dialog_set_font_name, iFpp)
GO(gtk_font_selection_dialog_set_preview_text, vFpp)
GO(gtk_font_selection_get_face, pFp)
GO(gtk_font_selection_get_face_list, pFp)
GO(gtk_font_selection_get_family, pFp)
GO(gtk_font_selection_get_family_list, pFp)
GO(gtk_font_selection_get_font, pFp) // Warning: failed to confirm
GO(gtk_font_selection_get_font_name, pFp)
GO(gtk_font_selection_get_preview_entry, pFp)
GO(gtk_font_selection_get_preview_text, pFp)
GO(gtk_font_selection_get_size, iFp)
GO(gtk_font_selection_get_size_entry, pFp)
GO(gtk_font_selection_get_size_list, pFp)
GO(gtk_font_selection_get_type, LFv)
GO(gtk_font_selection_new, pFv)
GO(gtk_font_selection_set_font_name, iFpp)
GO(gtk_font_selection_set_preview_text, vFpp)
GO(gtk_frame_get_label, pFp)
GO(gtk_frame_get_label_align, vFppp)
GO(gtk_frame_get_label_widget, pFp)
GO(gtk_frame_get_shadow_type, uFp)
GO(gtk_frame_get_type, LFv)
GO(gtk_frame_new, pFp)
GO(gtk_frame_set_label, vFpp)
GO(gtk_frame_set_label_align, vFpff)
GO(gtk_frame_set_label_widget, vFpp)
GO(gtk_frame_set_shadow_type, vFpu)
GO(gtk_gamma_curve_get_type, LFv) // Warning: failed to confirm
GO(gtk_gamma_curve_new, pFv) // Warning: failed to confirm
GO(gtk_gc_get, pFippu) // Warning: failed to confirm
GO(gtk_gc_release, vFp) // Warning: failed to confirm
GO(gtk_gesture_is_active, iFp)
GO(gtk_gesture_long_press_new, pFp)
GO(gtk_gesture_pan_new, pFpu)
GO(gtk_get_current_event, pFv)
GO(gtk_get_current_event_state, iFp)
GO(gtk_get_current_event_time, uFv)
GO(gtk_get_default_language, pFv)
GO(gtk_get_event_widget, pFp)
GO(gtk_get_binary_age, uFv)
GO(gtk_get_interface_age, uFv)
GO(gtk_get_major_version, uFv)
GO(gtk_get_minor_version, uFv)
GO(gtk_get_micro_version, uFv)
GO(gtk_get_option_group, pFi)
GO(gtk_grab_add, vFp)
GO(gtk_grab_get_current, pFv)
GO(gtk_grab_remove, vFp)
GO(gtk_grid_attach, vFppiiii)
GO(gtk_grid_get_type, LFv)
GO(gtk_grid_new, pFv)
GO(gtk_grid_set_column_homogeneous, vFpi)
GO(gtk_grid_set_column_spacing, vFpu)
GO(gtk_grid_set_row_homogeneous, vFpi)
GO(gtk_grid_set_row_spacing, vFpu)
GO(gtk_handle_box_get_child_detached, iFp)
GO(gtk_handle_box_get_handle_position, uFp)
GO(gtk_handle_box_get_shadow_type, uFp)
GO(gtk_handle_box_get_snap_edge, uFp)
GO(gtk_handle_box_get_type, LFv)
GO(gtk_handle_box_new, pFv)
GO(gtk_handle_box_set_handle_position, vFpu)
GO(gtk_handle_box_set_shadow_type, vFpu)
GO(gtk_handle_box_set_snap_edge, vFpu)
GO(gtk_hbox_get_type, LFv)
GO(gtk_hbox_new, pFii)
GO(gtk_hbutton_box_get_layout_default, iFv) // Warning: failed to confirm
GO(gtk_hbutton_box_get_spacing_default, iFv) // Warning: failed to confirm
GO(gtk_hbutton_box_get_type, LFv)
GO(gtk_hbutton_box_new, pFv)
GO(gtk_hbutton_box_set_layout_default, vFi) // Warning: failed to confirm
GO(gtk_hbutton_box_set_spacing_default, vFi) // Warning: failed to confirm
GO(gtk_header_bar_new, pFv)
GO(gtk_header_bar_get_type, LFv)
GO(gtk_header_bar_pack_end, vFpp)
GO(gtk_header_bar_set_show_close_button, vFpi)
GO(gtk_header_bar_set_title, vFpp)
GO(gtk_hpaned_get_type, LFv)
GO(gtk_hpaned_new, pFv)
GO(gtk_hruler_get_type, LFv) // Warning: failed to confirm
//GO(gtk_hruler_new, 
GO(gtk_hscale_get_type, LFv)
GO(gtk_hscale_new, pFp)
GO(gtk_hscale_new_with_range, pFddd)
GO(gtk_hscrollbar_get_type, LFv)
GO(gtk_hscrollbar_new, pFp)
GO(gtk_hseparator_get_type, LFv)
GO(gtk_hseparator_new, pFv)
GO(gtk_hsv_get_color, vFpppp)
GO(gtk_hsv_get_metrics, vFppp)
GO(gtk_hsv_get_type, LFv)
GO(gtk_hsv_is_adjusting, iFp)
GO(gtk_hsv_new, pFv)
GO(gtk_hsv_set_color, vFpddd)
GO(gtk_hsv_set_metrics, vFpii)
GO(gtk_hsv_to_rgb, vFdddppp)
GO(gtk_icon_factory_add, vFppp)
GO(gtk_icon_factory_add_default, vFp)
GO(gtk_icon_factory_get_type, LFv)
GO(gtk_icon_factory_lookup, pFpp)
GO(gtk_icon_factory_lookup_default, pFp)
GO(gtk_icon_factory_new, pFv)
GO(gtk_icon_factory_remove_default, vFp)
GO(gtk_icon_info_copy, pFp)
GO(gtk_icon_info_free, vFp)
GO(gtk_icon_info_get_attach_points, iFppp)
GO(gtk_icon_info_get_base_size, iFp)
GO(gtk_icon_info_get_builtin_pixbuf, pFp)
GO(gtk_icon_info_get_display_name, pFp)
GO(gtk_icon_info_get_embedded_rect, iFpp)
GO(gtk_icon_info_get_filename, pFp)
GO(gtk_icon_info_get_type, LFv)
GO(gtk_icon_info_load_icon, pFpp)
GO(gtk_icon_info_load_surface, pFppp)
GO(gtk_icon_info_load_symbolic_for_context, pFpppp)
GO(gtk_icon_info_new_for_pixbuf, pFpp)
GO(gtk_icon_info_set_raw_coordinates, vFpi)
GO(gtk_icon_lookup_flags_get_type, LFv)
GO(gtk_icon_set_add_source, vFpp)
GO(gtk_icon_set_copy, pFp)
GO(gtk_icon_set_get_sizes, vFppp)
GO(gtk_icon_set_get_type, LFv)
GO(gtk_icon_set_new, pFv)
GO(gtk_icon_set_new_from_pixbuf, pFp)
GO(gtk_icon_set_ref, pFp)
GO(gtk_icon_set_render_icon, pFppuuupp)
GO(gtk_icon_set_unref, vFp)
GO(gtk_icon_size_from_name, uFp)
GO(gtk_icon_size_get_name, pFu)
GO(gtk_icon_size_get_type, LFv)
GO(gtk_icon_size_lookup, iFupp)
GO(gtk_icon_size_lookup_for_settings, iFpupp)
GO(gtk_icon_size_register, uFpii)
GO(gtk_icon_size_register_alias, vFpu)
GO(gtk_icon_source_copy, pFp)
GO(gtk_icon_source_free, vFp)
GO(gtk_icon_source_get_direction, uFp)
GO(gtk_icon_source_get_direction_wildcarded, iFp)
GO(gtk_icon_source_get_filename, pFp)
GO(gtk_icon_source_get_icon_name, pFp)
GO(gtk_icon_source_get_pixbuf, pFp)
GO(gtk_icon_source_get_size, uFp)
GO(gtk_icon_source_get_size_wildcarded, iFp)
GO(gtk_icon_source_get_state, uFp)
GO(gtk_icon_source_get_state_wildcarded, iFp)
GO(gtk_icon_source_get_type, LFv)
GO(gtk_icon_source_new, pFv)
GO(gtk_icon_source_set_direction, vFpu)
GO(gtk_icon_source_set_direction_wildcarded, vFpi)
GO(gtk_icon_source_set_filename, vFpp)
GO(gtk_icon_source_set_icon_name, vFpp)
GO(gtk_icon_source_set_pixbuf, vFpp)
GO(gtk_icon_source_set_size, vFpu)
GO(gtk_icon_source_set_size_wildcarded, vFpi)
GO(gtk_icon_source_set_state, vFpu)
GO(gtk_icon_source_set_state_wildcarded, vFpi)
GO(gtk_icon_theme_add_builtin_icon, vFpip)
GO(gtk_icon_theme_append_search_path, vFpp)
GO(gtk_icon_theme_choose_icon, pFppiu)
GO(gtk_icon_theme_error_get_type, LFv)
GO(gtk_icon_theme_error_quark, uFv)
GO(gtk_icon_theme_get_default, pFv)
GO(gtk_icon_theme_get_example_icon_name, pFp)
GO(gtk_icon_theme_get_for_display, pFp) // Warning: failed to confirm
GO(gtk_icon_theme_get_for_screen, pFp)
GO(gtk_icon_theme_get_icon_sizes, pFpp)
GO(gtk_icon_theme_get_search_path, vFppp)
GO(gtk_icon_theme_get_type, LFv)
GO(gtk_icon_theme_has_icon, iFpp)
GO(gtk_icon_theme_list_contexts, pFp)
GO(gtk_icon_theme_list_icons, pFpp)
GO(gtk_icon_theme_load_icon, pFppiup)
GO(gtk_icon_theme_lookup_by_gicon, pFppiu)
GO(gtk_icon_theme_lookup_icon, pFppiu)
GO(gtk_icon_theme_lookup_icon_for_scale, pFppiiu)
GO(gtk_icon_theme_new, pFv)
GO(gtk_icon_theme_prepend_search_path, vFpp)
GO(gtk_icon_theme_rescan_if_needed, iFp)
GO(gtk_icon_theme_set_custom_theme, vFpp)
GO(gtk_icon_theme_set_screen, vFpp)
GO(gtk_icon_theme_set_search_path, vFppi)
GO(gtk_icon_view_convert_widget_to_bin_window_coords, vFpiipp)
GO(gtk_icon_view_create_drag_icon, pFpp)
GO(gtk_icon_view_drop_position_get_type, LFv)
GO(gtk_icon_view_enable_model_drag_dest, vFppiu)
GO(gtk_icon_view_enable_model_drag_source, vFpupiu)
GO(gtk_icon_view_get_columns, iFp)
GO(gtk_icon_view_get_column_spacing, iFp)
GO(gtk_icon_view_get_cursor, iFppp)
GO(gtk_icon_view_get_dest_item_at_pos, iFpiipp)
GO(gtk_icon_view_get_drag_dest_item, vFppp)
GO(gtk_icon_view_get_item_at_pos, iFpiipp)
GO(gtk_icon_view_get_item_column, iFpp)
GO(gtk_icon_view_get_item_orientation, uFp)
GO(gtk_icon_view_get_item_padding, iFp)
GO(gtk_icon_view_get_item_row, iFpp)
GO(gtk_icon_view_get_item_width, iFp)
GO(gtk_icon_view_get_margin, iFp)
GO(gtk_icon_view_get_markup_column, iFp)
GO(gtk_icon_view_get_model, pFp)
GO(gtk_icon_view_get_orientation, iFp) // Warning: failed to confirm
GO(gtk_icon_view_get_path_at_pos, pFpii)
GO(gtk_icon_view_get_pixbuf_column, iFp)
GO(gtk_icon_view_get_reorderable, iFp)
GO(gtk_icon_view_get_row_spacing, iFp)
GO(gtk_icon_view_get_selected_items, pFp)
GO(gtk_icon_view_get_selection_mode, uFp)
GO(gtk_icon_view_get_spacing, iFp)
GO(gtk_icon_view_get_text_column, iFp)
GO(gtk_icon_view_get_tooltip_column, iFp)
GO(gtk_icon_view_get_tooltip_context, iFpppippp)
GO(gtk_icon_view_get_type, LFv)
GO(gtk_icon_view_get_visible_range, iFppp)
GO(gtk_icon_view_item_activated, vFpp)
GO(gtk_icon_view_new, pFv)
GO(gtk_icon_view_new_with_model, pFp)
GO(gtk_icon_view_path_is_selected, iFpp)
GO(gtk_icon_view_scroll_to_path, vFppiff)
GO(gtk_icon_view_select_all, vFp)
//GOM(gtk_icon_view_selected_foreach, vFppp)
GO(gtk_icon_view_select_path, vFpp)
GO(gtk_icon_view_set_columns, vFpi)
GO(gtk_icon_view_set_column_spacing, vFpi)
GO(gtk_icon_view_set_cursor, vFpppi)
GO(gtk_icon_view_set_drag_dest_item, vFppu)
GO(gtk_icon_view_set_item_orientation, vFpu)
GO(gtk_icon_view_set_item_padding, vFpi)
GO(gtk_icon_view_set_item_width, vFpi)
GO(gtk_icon_view_set_margin, vFpi)
GO(gtk_icon_view_set_markup_column, vFpi)
GO(gtk_icon_view_set_model, vFpp)
GO(gtk_icon_view_set_orientation, vFpi) // Warning: failed to confirm
GO(gtk_icon_view_set_pixbuf_column, vFpi)
GO(gtk_icon_view_set_reorderable, vFpi)
GO(gtk_icon_view_set_row_spacing, vFpi)
GO(gtk_icon_view_set_selection_mode, vFpu)
GO(gtk_icon_view_set_spacing, vFpi)
GO(gtk_icon_view_set_text_column, vFpi)
GO(gtk_icon_view_set_tooltip_cell, vFpppp)
GO(gtk_icon_view_set_tooltip_column, vFpi)
GO(gtk_icon_view_set_tooltip_item, vFppp)
GO(gtk_icon_view_unselect_all, vFp)
GO(gtk_icon_view_unselect_path, vFpp)
GO(gtk_icon_view_unset_model_drag_dest, vFp)
GO(gtk_icon_view_unset_model_drag_source, vFp)
GO(gtk_identifier_get_type, LFv) // Warning: failed to confirm
//GOM(gtk_idle_add, uFEBp)
//GOM(gtk_idle_add_full, uFEiBppB)
//GOM(gtk_idle_add_priority, uFEiBp)
GO(gtk_idle_remove, vFu) // Warning: failed to confirm
GO(gtk_idle_remove_by_data, vFp) // Warning: failed to confirm
GO(gtk_image_clear, vFp)
GO(gtk_image_get, vFppp) // Warning: failed to confirm
GO(gtk_image_get_animation, pFp)
GO(gtk_image_get_gicon, vFppp)
GO(gtk_image_get_icon_name, vFppp)
GO(gtk_image_get_icon_set, vFppp)
GO(gtk_image_get_image, vFppp) // Warning: failed to confirm
GO(gtk_image_get_pixbuf, pFp)
GO(gtk_image_get_pixel_size, iFp)
GO(gtk_image_get_pixmap, vFppp) // Warning: failed to confirm
GO(gtk_image_get_stock, vFppp)
GO(gtk_image_get_storage_type, uFp)
GO(gtk_image_get_type, LFv)
GO(gtk_image_menu_item_get_always_show_image, iFp)
GO(gtk_image_menu_item_get_image, pFp)
GO(gtk_image_menu_item_get_type, LFv)
GO(gtk_image_menu_item_get_use_stock, iFp)
GO(gtk_image_menu_item_new, pFv)
GO(gtk_image_menu_item_new_from_stock, pFpp)
GO(gtk_image_menu_item_new_with_label, pFp)
GO(gtk_image_menu_item_new_with_mnemonic, pFp)
GO(gtk_image_menu_item_set_accel_group, vFpp)
GO(gtk_image_menu_item_set_always_show_image, vFpi)
GO(gtk_image_menu_item_set_image, vFpp)
GO(gtk_image_menu_item_set_use_stock, vFpi)
GO(gtk_image_new, pFv)
GO(gtk_image_new_from_animation, pFp)
GO(gtk_image_new_from_file, pFp)
GO(gtk_image_new_from_gicon, pFpu)
GO(gtk_image_new_from_icon_name, pFpu)
GO(gtk_image_new_from_icon_set, pFpu)
GO(gtk_image_new_from_image, pFpp) // Warning: failed to confirm
GO(gtk_image_new_from_pixbuf, pFp)
GO(gtk_image_new_from_pixmap, pFpp) // Warning: failed to confirm
GO(gtk_image_new_from_stock, pFpu)
GO(gtk_image_set, vFppp) // Warning: failed to confirm
GO(gtk_image_set_from_animation, vFpp)
GO(gtk_image_set_from_file, vFpp)
GO(gtk_image_set_from_gicon, vFppu)
GO(gtk_image_set_from_icon_name, vFppu)
GO(gtk_image_set_from_icon_set, vFppu)
GO(gtk_image_set_from_image, vFppp) // Warning: failed to confirm
GO(gtk_image_set_from_pixbuf, vFpp)
GO(gtk_image_set_from_pixmap, vFppp) // Warning: failed to confirm
GO(gtk_image_set_from_stock, vFppu)
GO(gtk_image_set_pixel_size, vFpi)
GO(gtk_image_type_get_type, LFv)
GO(gtk_im_context_delete_surrounding, iFpii)
GO(gtk_im_context_filter_key, iFpippuuii) // Warning: failed to confirm
GO(gtk_im_context_filter_keypress, iFpp)
GO(gtk_im_context_focus_in, vFp)
GO(gtk_im_context_focus_out, vFp)
GO(gtk_im_context_get_preedit_string, vFpppp)
GO(gtk_im_context_get_surrounding, iFppp)
GO(gtk_im_context_get_type, LFv)
GO(gtk_im_context_reset, vFp)
GO(gtk_im_context_set_client_widget, vFpp) // Warning: failed to confirm
GO(gtk_im_context_set_client_window, vFpp)
GO(gtk_im_context_set_cursor_location, vFpp)
GO(gtk_im_context_set_surrounding, vFppii)
GO(gtk_im_context_set_use_preedit, vFpi)
GO(gtk_im_context_simple_add_table, vFppii)
GO(gtk_im_context_simple_get_type, LFv)
GO(gtk_im_context_simple_new, pFv)
GO(gtk_im_multicontext_append_menuitems, vFpp)
GO(gtk_im_multicontext_get_context_id, pFp)
GO(gtk_im_multicontext_get_type, LFv)
GO(gtk_im_multicontext_new, pFv)
GO(gtk_im_multicontext_set_context_id, vFpp)
GO(gtk_im_preedit_style_get_type, LFv)
GO(gtk_im_status_style_get_type, LFv)
GO(gtk_info_bar_add_action_widget, vFppi)
GO(gtk_info_bar_add_button, pFppi)
//GOM(gtk_info_bar_add_buttons, vFppV)
GO(gtk_info_bar_get_action_area, pFp)
GO(gtk_info_bar_get_content_area, pFp)
GO(gtk_info_bar_get_message_type, uFp)
GO(gtk_info_bar_get_type, LFv)
GO(gtk_info_bar_new, pFv)
//GOM(gtk_info_bar_new_with_buttons, pFpV)
GO(gtk_info_bar_response, vFpi)
GO(gtk_info_bar_set_default_response, vFpi)
GO(gtk_info_bar_set_message_type, vFpu)
GO(gtk_info_bar_set_response_sensitive, vFpii)
GOM(gtk_init, vFEpp)
//GO(gtk_init_add, 
GOM(gtk_init_check, iFEpp)
GOM(gtk_init_with_args, iFEpppppp)
//GOM(gtk_input_add_full, uFEiBBppB)
GO(gtk_input_dialog_get_type, LFv) // Warning: failed to confirm
GO(gtk_input_dialog_new, pFv) // Warning: failed to confirm
GO(gtk_input_hints_get_type, LFv)
GO(gtk_input_purpose_get_type, LFv)
GO(gtk_input_remove, vFu) // Warning: failed to confirm
GO(gtk_invisible_get_screen, pFp)
GO(gtk_invisible_get_type, LFv)
GO(gtk_invisible_new, pFv)
GO(gtk_invisible_new_for_screen, pFp)
GO(gtk_invisible_set_screen, vFpp)
//GO(gtk_item_deselect, 
//GO(gtk_item_factories_path_delete, 
//GO(gtk_item_factory_add_foreign, 
//GO(gtk_item_factory_construct, 
//GO(gtk_item_factory_create_item, 
//GO(gtk_item_factory_create_items, 
//GO(gtk_item_factory_create_items_ac, 
//GO(gtk_item_factory_create_menu_entries, 
//GO(gtk_item_factory_delete_entries, 
//GO(gtk_item_factory_delete_entry, 
//GO(gtk_item_factory_delete_item, 
//GO(gtk_item_factory_from_path, 
//GO(gtk_item_factory_from_widget, 
//GO(gtk_item_factory_get_item, 
//GO(gtk_item_factory_get_item_by_action, 
GO(gtk_item_factory_get_type, LFv) // Warning: failed to confirm
//GO(gtk_item_factory_get_widget, 
//GO(gtk_item_factory_get_widget_by_action, 
//GO(gtk_item_factory_new, 
//GO(gtk_item_factory_path_from_widget, 
//GO(gtk_item_factory_popup, 
//GO(gtk_item_factory_popup_data, 
//GO(gtk_item_factory_popup_data_from_widget, 
//GO(gtk_item_factory_popup_with_data, 
//GO(gtk_item_factory_set_translate_func, 
GO(gtk_item_get_type, LFv) // Warning: failed to confirm
//GO(gtk_item_select, 
//GO(gtk_item_toggle, 
GO(gtk_justification_get_type, LFv)
//GOM(gtk_key_snooper_install, uFEpp)
GO(gtk_key_snooper_remove, vFu)
GO(gtk_label_get, vFpp) // Warning: failed to confirm
GO(gtk_label_get_angle, dFp)
GO(gtk_label_get_attributes, pFp)
GO(gtk_label_get_current_uri, pFp)
GO(gtk_label_get_ellipsize, uFp)
GO(gtk_label_get_justify, uFp)
GO(gtk_label_get_label, pFp)
GO(gtk_label_get_layout, pFp)
GO(gtk_label_get_layout_offsets, vFppp)
GO(gtk_label_get_line_wrap, iFp)
GO(gtk_label_get_line_wrap_mode, uFp)
GO(gtk_label_get_max_width_chars, iFp)
GO(gtk_label_get_mnemonic_keyval, uFp)
GO(gtk_label_get_mnemonic_widget, pFp)
GO(gtk_label_get_selectable, iFp)
GO(gtk_label_get_selection_bounds, iFppp)
GO(gtk_label_get_single_line_mode, iFp)
GO(gtk_label_get_text, pFp)
GO(gtk_label_get_track_visited_links, iFp)
GO(gtk_label_get_type, LFv)
GO(gtk_label_get_use_markup, iFp)
GO(gtk_label_get_use_underline, iFp)
GO(gtk_label_get_width_chars, iFp)
GO(gtk_label_new, pFp)
GO(gtk_label_new_with_mnemonic, pFp)
GO(gtk_label_parse_uline, uFpp) // Warning: failed to confirm
GO(gtk_label_select_region, vFpii)
GO(gtk_label_set_angle, vFpd)
GO(gtk_label_set_attributes, vFpp)
GO(gtk_label_set_ellipsize, vFpu)
GO(gtk_label_set_justify, vFpu)
GO(gtk_label_set_label, vFpp)
GO(gtk_label_set_line_wrap, vFpi)
GO(gtk_label_set_line_wrap_mode, vFpu)
GO(gtk_label_set_markup, vFpp)
GO(gtk_label_set_markup_with_mnemonic, vFpp)
GO(gtk_label_set_max_width_chars, vFpi)
GO(gtk_label_set_mnemonic_widget, vFpp)
GO(gtk_label_set_pattern, vFpp)
GO(gtk_label_set_selectable, vFpi)
GO(gtk_label_set_single_line_mode, vFpi)
GO(gtk_label_set_text, vFpp)
GO(gtk_label_set_text_with_mnemonic, vFpp)
GO(gtk_label_set_track_visited_links, vFpi)
GO(gtk_label_set_use_markup, vFpi)
GO(gtk_label_set_use_underline, vFpi)
GO(gtk_label_set_width_chars, vFpi)
GO(gtk_label_set_xalign, vFpf)
//GO(gtk_layout_freeze, 
GO(gtk_layout_get_bin_window, pFp)
GO(gtk_layout_get_hadjustment, pFp)
GO(gtk_layout_get_size, vFppp)
GO(gtk_layout_get_type, LFv)
GO(gtk_layout_get_vadjustment, pFp)
GO(gtk_layout_move, vFppii)
GO(gtk_layout_new, pFpp)
GO(gtk_layout_put, vFppii)
GO(gtk_layout_set_hadjustment, vFpp)
GO(gtk_layout_set_size, vFpuu)
GO(gtk_layout_set_vadjustment, vFpp)
//GO(gtk_layout_thaw, 
GO(gtk_level_bar_mode_get_type, LFv)
GO(gtk_level_bar_get_type, LFv)
GO(gtk_license_get_type, LFv)
GO(gtk_link_button_get_type, LFv)
GO(gtk_link_button_get_uri, pFp)
GO(gtk_link_button_get_visited, iFp)
GO(gtk_link_button_new, pFp)
GO(gtk_link_button_new_with_label, pFpp)
GO(gtk_link_button_set_uri, vFpp)
//GO(gtk_link_button_set_uri_hook, 
GO(gtk_link_button_set_visited, vFpi)
GO(gtk_list_append_items, vFpp) // Warning: failed to confirm
GO(gtk_list_box_get_type, LFv)
GO(gtk_list_box_row_get_type, LFv)
GOM(gtk_list_box_set_header_func, vFEpppp)
GO(gtk_list_child_position, iFpp) // Warning: failed to confirm
GO(gtk_list_clear_items, vFpii) // Warning: failed to confirm
GO(gtk_list_end_drag_selection, vFp) // Warning: failed to confirm
GO(gtk_list_end_selection, vFp) // Warning: failed to confirm
GO(gtk_list_extend_selection, vFpifi) // Warning: failed to confirm
GO(gtk_list_get_type, LFv) // Warning: failed to confirm
GO(gtk_list_insert_items, vFppi) // Warning: failed to confirm
GO(gtk_list_item_deselect, vFp) // Warning: failed to confirm
GO(gtk_list_item_get_type, LFv) // Warning: failed to confirm
GO(gtk_list_item_new, pFv) // Warning: failed to confirm
GO(gtk_list_item_new_with_label, pFp) // Warning: failed to confirm
GO(gtk_list_item_select, vFp) // Warning: failed to confirm
GO(gtk_list_new, pFv) // Warning: failed to confirm
GO(gtk_list_prepend_items, vFpp) // Warning: failed to confirm
GO(gtk_list_remove_items, vFpp) // Warning: failed to confirm
GO(gtk_list_remove_items_no_unref, vFpp) // Warning: failed to confirm
GO(gtk_list_scroll_horizontal, vFpif) // Warning: failed to confirm
GO(gtk_list_scroll_vertical, vFpif) // Warning: failed to confirm
GO(gtk_list_select_all, vFp) // Warning: failed to confirm
GO(gtk_list_select_child, vFpp) // Warning: failed to confirm
GO(gtk_list_select_item, vFpi) // Warning: failed to confirm
GO(gtk_list_set_selection_mode, vFpi) // Warning: failed to confirm
GO(gtk_list_start_selection, vFp) // Warning: failed to confirm
GO(gtk_list_store_append, vFpp)
GO(gtk_list_store_clear, vFp)
GO(gtk_list_store_get_type, LFv)
GO(gtk_list_store_insert, vFppi)
GO(gtk_list_store_insert_after, vFppp)
GO(gtk_list_store_insert_before, vFppp)
GOM(gtk_list_store_insert_with_values, vFEppiV)
GO(gtk_list_store_insert_with_valuesv, vFppippi)
GO(gtk_list_store_iter_is_valid, iFpp)
GO(gtk_list_store_move_after, vFppp)
GO(gtk_list_store_move_before, vFppp)
GO2(gtk_list_store_new, pFiV, gtk_list_store_newv)
GO(gtk_list_store_newv, pFip)
GO(gtk_list_store_prepend, vFpp)
GO(gtk_list_store_remove, iFpp)
GO(gtk_list_store_reorder, vFpp)
//GO2(gtk_list_store_set, vFppV, gtk_list_store_set_valist)
GO(gtk_list_store_set_column_types, vFpip)
//GOM(gtk_list_store_set_valist, vFppA)
GO(gtk_list_store_set_value, vFppip)
GO(gtk_list_store_set_valuesv, vFppppi)
GO(gtk_list_store_swap, vFppp)
GO(gtk_list_toggle_add_mode, vFp) // Warning: failed to confirm
GO(gtk_list_toggle_focus_row, vFp) // Warning: failed to confirm
GO(gtk_list_toggle_row, vFpp) // Warning: failed to confirm
GO(gtk_list_undo_selection, vFp) // Warning: failed to confirm
GO(gtk_list_unselect_all, vFp) // Warning: failed to confirm
GO(gtk_list_unselect_child, vFpp) // Warning: failed to confirm
GO(gtk_list_unselect_item, vFpi) // Warning: failed to confirm
GO(gtk_main, vFv)
GO(gtk_main_do_event, vFp)
GO(gtk_main_iteration, iFv)
GO(gtk_main_iteration_do, iFi)
GO(gtk_main_level, uFv)
GO(gtk_main_quit, vFv)
//GO(gtk_marshal_BOOLEAN__POINTER, 
//GO(gtk_marshal_BOOLEAN__POINTER_INT_INT, 
//GO(gtk_marshal_BOOLEAN__POINTER_INT_INT_UINT, 
//GO(gtk_marshal_BOOLEAN__POINTER_POINTER_INT_INT, 
//GO(gtk_marshal_BOOLEAN__POINTER_STRING_STRING_POINTER, 
//GO(gtk_marshal_BOOLEAN__VOID, 
//GO(gtk_marshal_ENUM__ENUM, 
//GO(gtk_marshal_INT__POINTER, 
//GO(gtk_marshal_INT__POINTER_CHAR_CHAR, 
//GO(gtk_marshal_VOID__ENUM_FLOAT, 
//GO(gtk_marshal_VOID__ENUM_FLOAT_BOOLEAN, 
//GO(gtk_marshal_VOID__INT_INT, 
//GO(gtk_marshal_VOID__INT_INT_POINTER, 
//GO(gtk_marshal_VOID__POINTER_INT, 
//GO(gtk_marshal_VOID__POINTER_INT_INT_POINTER_UINT_UINT, 
//GO(gtk_marshal_VOID__POINTER_POINTER, 
//GO(gtk_marshal_VOID__POINTER_POINTER_POINTER, 
//GO(gtk_marshal_VOID__POINTER_POINTER_UINT_UINT, 
//GO(gtk_marshal_VOID__POINTER_STRING_STRING, 
//GO(gtk_marshal_VOID__POINTER_UINT, 
//GO(gtk_marshal_VOID__POINTER_UINT_ENUM, 
//GO(gtk_marshal_VOID__POINTER_UINT_UINT, 
//GO(gtk_marshal_VOID__STRING_INT_POINTER, 
//GO(gtk_marshal_VOID__UINT_POINTER_UINT_ENUM_ENUM_POINTER, 
//GO(gtk_marshal_VOID__UINT_POINTER_UINT_UINT_ENUM, 
//GO(gtk_marshal_VOID__UINT_STRING, 
GO(gtk_match_type_get_type, LFv) // Warning: failed to confirm
GO(gtk_menu_attach, vFppuuuu)
GOM(gtk_menu_attach_to_widget, vFEppp)
GO(gtk_menu_bar_get_child_pack_direction, uFp)
GO(gtk_menu_bar_get_pack_direction, uFp)
GO(gtk_menu_bar_get_type, LFv)
GO(gtk_menu_bar_new, pFv)
GO(gtk_menu_bar_set_child_pack_direction, vFpu)
GO(gtk_menu_bar_set_pack_direction, vFpu)
GO(gtk_menu_button_new, pFv)
GO(gtk_menu_button_set_menu_model, vFpp)
GO(gtk_menu_button_get_type, LFv)
GO(gtk_menu_detach, vFp)
GO(gtk_menu_direction_type_get_type, LFv)
GO(gtk_menu_get_accel_group, pFp)
GO(gtk_menu_get_accel_path, pFp)
GO(gtk_menu_get_active, pFp)
GO(gtk_menu_get_attach_widget, pFp)
GO(gtk_menu_get_for_attach_widget, pFp)
GO(gtk_menu_get_monitor, iFp)
GO(gtk_menu_get_reserve_toggle_size, iFp)
GO(gtk_menu_get_tearoff_state, iFp)
GO(gtk_menu_get_title, pFp)
GO(gtk_menu_get_type, LFv)
GO(gtk_menu_item_activate, vFp)
GO(gtk_menu_item_deselect, vFp)
GO(gtk_menu_item_get_accel_path, pFp)
GO(gtk_menu_item_get_label, pFp)
GO(gtk_menu_item_get_right_justified, iFp)
GO(gtk_menu_item_get_submenu, pFp)
GO(gtk_menu_item_get_type, LFv)
GO(gtk_menu_item_get_use_underline, iFp)
GO(gtk_menu_item_new, pFv)
GO(gtk_menu_item_new_with_label, pFp)
GO(gtk_menu_item_new_with_mnemonic, pFp)
GO(gtk_menu_item_remove_submenu, pFp) // Warning: failed to confirm
GO(gtk_menu_item_select, vFp)
GO(gtk_menu_item_set_accel_path, vFpp)
GO(gtk_menu_item_set_label, vFpp)
GO(gtk_menu_item_set_right_justified, vFpi)
GO(gtk_menu_item_set_submenu, vFpp)
GO(gtk_menu_item_set_use_underline, vFpi)
GO(gtk_menu_item_toggle_size_allocate, vFpi)
GO(gtk_menu_item_toggle_size_request, vFpp)
GO(gtk_menu_new, pFv)
GO(gtk_menu_popdown, vFp)
GOM(gtk_menu_popup, vFEpppppuu)
GO(gtk_menu_reorder_child, vFppi)
GO(gtk_menu_reposition, vFp)
GO(gtk_menu_set_accel_group, vFpp)
GO(gtk_menu_set_accel_path, vFpp)
GO(gtk_menu_set_active, vFpu)
GO(gtk_menu_set_monitor, vFpi)
GO(gtk_menu_set_reserve_toggle_size, vFpi)
GO(gtk_menu_set_screen, vFpp)
GO(gtk_menu_set_tearoff_state, vFpi)
GO(gtk_menu_set_title, vFpp)
GO(gtk_menu_shell_activate_item, vFppi)
GO(gtk_menu_shell_append, vFpp)
GO(gtk_menu_shell_cancel, vFp)
GO(gtk_menu_shell_deactivate, vFp)
GO(gtk_menu_shell_deselect, vFp)
GO(gtk_menu_shell_get_take_focus, iFp)
GO(gtk_menu_shell_get_type, LFv)
GO(gtk_menu_shell_insert, vFppi)
GO(gtk_menu_shell_prepend, vFpp)
GO(gtk_menu_shell_select_first, vFpi)
GO(gtk_menu_shell_select_item, vFpp)
GO(gtk_menu_shell_set_take_focus, vFpi)
GO(gtk_menu_tool_button_get_menu, pFp)
GO(gtk_menu_tool_button_get_type, LFv)
GO(gtk_menu_tool_button_new, pFpp)
GO(gtk_menu_tool_button_new_from_stock, pFp)
//GO(gtk_menu_tool_button_set_arrow_tooltip, 
GO(gtk_menu_tool_button_set_arrow_tooltip_markup, vFpp)
GO(gtk_menu_tool_button_set_arrow_tooltip_text, vFpp)
GO(gtk_menu_tool_button_set_menu, vFpp)
GOM(gtk_message_dialog_format_secondary_markup, vFEppV)
GOM(gtk_message_dialog_format_secondary_text, vFEppV)
GO(gtk_message_dialog_get_image, pFp)
GO(gtk_message_dialog_get_message_area, pFp)
GO(gtk_message_dialog_get_type, LFv)
GO(gtk_message_dialog_new, pFpuiippppppppppp)   // vaarg :(
GO(gtk_message_dialog_new_with_markup, pFpuiippppppppppp)   // vaarg
GO(gtk_message_dialog_set_image, vFpp)
GO(gtk_message_dialog_set_markup, vFpp)
GO(gtk_message_type_get_type, LFv)
GO(gtk_metric_type_get_type, LFv) // Warning: failed to confirm
GO(gtk_misc_get_alignment, vFppp)
GO(gtk_misc_get_padding, vFppp)
GO(gtk_misc_get_type, LFv)
GO(gtk_misc_set_alignment, vFpff)
GO(gtk_misc_set_padding, vFpii)
GO(gtk_mount_operation_get_parent, pFp)
GO(gtk_mount_operation_get_screen, pFp)
GO(gtk_mount_operation_get_type, LFv)
GO(gtk_mount_operation_is_showing, iFp)
GO(gtk_mount_operation_new, pFp)
GO(gtk_mount_operation_set_parent, vFpp)
GO(gtk_mount_operation_set_screen, vFpp)
GO(gtk_movement_step_get_type, LFv)
GO(gtk_native_dialog_destroy, vFp)
GO(gtk_native_dialog_get_modal, iFp)
GO(gtk_native_dialog_get_title, pFp)
GO(gtk_native_dialog_get_transient_for, pFp)
GO(gtk_native_dialog_get_visible, iFp)
GO(gtk_native_dialog_hide, vFp)
GO(gtk_native_dialog_run, iFp)
GO(gtk_native_dialog_set_modal, vFpi)
GO(gtk_native_dialog_set_title, vFpp)
GO(gtk_native_dialog_set_transient_for, vFpp)
GO(gtk_native_dialog_show, vFp)
GO(gtk_native_get_surface, pFp) // Warning: failed to confirm
GO(gtk_notebook_append_page, iFppp)
GO(gtk_notebook_append_page_menu, iFpppp)
GO(gtk_notebook_get_action_widget, pFpu)
GO(gtk_notebook_get_current_page, iFp)
GO(gtk_notebook_get_group, pFp) // Warning: failed to confirm
GO(gtk_notebook_get_group_id, iFp) // Warning: failed to confirm
GO(gtk_notebook_get_group_name, pFp)
GO(gtk_notebook_get_menu_label, pFpp)
GO(gtk_notebook_get_menu_label_text, pFpp)
GO(gtk_notebook_get_n_pages, iFp)
GO(gtk_notebook_get_nth_page, pFpi)
GO(gtk_notebook_get_scrollable, iFp)
GO(gtk_notebook_get_show_border, iFp)
GO(gtk_notebook_get_show_tabs, iFp)
GO(gtk_notebook_get_tab_detachable, iFpp)
GO(gtk_notebook_get_tab_hborder, WFp)
GO(gtk_notebook_get_tab_label, pFpp)
GO(gtk_notebook_get_tab_label_text, pFpp)
GO(gtk_notebook_get_tab_pos, uFp)
GO(gtk_notebook_get_tab_reorderable, iFpp)
GO(gtk_notebook_get_tab_vborder, WFp)
GO(gtk_notebook_get_type, LFv)
GO(gtk_notebook_insert_page, iFpppi)
GO(gtk_notebook_insert_page_menu, iFppppi)
GO(gtk_notebook_new, pFv)
GO(gtk_notebook_next_page, vFp)
GO(gtk_notebook_page_num, iFpp)
GO(gtk_notebook_popup_disable, vFp)
GO(gtk_notebook_popup_enable, vFp)
GO(gtk_notebook_prepend_page, iFppp)
GO(gtk_notebook_prepend_page_menu, iFpppp)
GO(gtk_notebook_prev_page, vFp)
GO(gtk_notebook_query_tab_label_packing, vFppppp) // Warning: failed to confirm
GO(gtk_notebook_remove_page, vFpi)
GO(gtk_notebook_reorder_child, vFppi)
GO(gtk_notebook_set_action_widget, vFppu)
GO(gtk_notebook_set_current_page, vFpi)
GO(gtk_notebook_set_group, vFpp) // Warning: failed to confirm
GO(gtk_notebook_set_group_id, vFpi) // Warning: failed to confirm
GO(gtk_notebook_set_group_name, vFpp)
GO(gtk_notebook_set_homogeneous_tabs, vFpi) // Warning: failed to confirm
GO(gtk_notebook_set_menu_label, vFppp)
GO(gtk_notebook_set_menu_label_text, vFppp)
GO(gtk_notebook_set_scrollable, vFpi)
GO(gtk_notebook_set_show_border, vFpi)
GO(gtk_notebook_set_show_tabs, vFpi)
GO(gtk_notebook_set_tab_border, vFpu) // Warning: failed to confirm
GO(gtk_notebook_set_tab_detachable, vFppi)
GO(gtk_notebook_set_tab_hborder, vFpu) // Warning: failed to confirm
GO(gtk_notebook_set_tab_label, vFppp)
GO(gtk_notebook_set_tab_label_packing, vFppiii) // Warning: failed to confirm
GO(gtk_notebook_set_tab_label_text, vFppp)
GO(gtk_notebook_set_tab_pos, vFpu)
GO(gtk_notebook_set_tab_reorderable, vFppi)
GO(gtk_notebook_set_tab_vborder, vFpu) // Warning: failed to confirm
//GOM(gtk_notebook_set_window_creation_hook, pFEppp)
GO(gtk_notebook_tab_get_type, LFv)
GO(gtk_number_up_layout_get_type, LFv)
GO(gtk_object_add_arg_type, vFpiuu) // Warning: failed to confirm
GO(gtk_object_destroy, vFp) // Warning: failed to confirm
GO(gtk_object_flags_get_type, LFv) // Warning: failed to confirm
GO(gtk_object_get, vFppppppppppp) // Warning: failed to confirm
GO(gtk_object_get_data, pFpp) // Warning: failed to confirm
GO(gtk_object_get_data_by_id, pFpp) // Warning: failed to confirm
GO(gtk_object_get_type, LFv) // Warning: failed to confirm
GO(gtk_object_get_user_data, pFp) // Warning: failed to confirm
GO(gtk_object_new, pFppppppppppp) // Warning: failed to confirm
GO(gtk_object_ref, pFp) // Warning: failed to confirm
GO(gtk_object_remove_data, vFpp) // Warning: failed to confirm
GO(gtk_object_remove_data_by_id, vFpp) // Warning: failed to confirm
GO(gtk_object_remove_no_notify, vFpp) // Warning: failed to confirm
GO(gtk_object_remove_no_notify_by_id, vFpp) // Warning: failed to confirm
GO(gtk_object_set, vFppppppppppp) // Warning: failed to confirm
GO(gtk_object_set_data, vFppp) // Warning: failed to confirm
GO(gtk_object_set_data_by_id, vFppp) // Warning: failed to confirm
//GOM(gtk_object_set_data_by_id_full, vFEpppp)
GOM(gtk_object_set_data_full, vFEpppp) // Warning: failed to confirm
GO(gtk_object_set_user_data, vFpp) // Warning: failed to confirm
GO(gtk_object_sink, vFp) // Warning: failed to confirm
GO(gtk_object_unref, vFp) // Warning: failed to confirm
//GOM(gtk_object_weakref, vFEppp)
//GOM(gtk_object_weakunref, vFEppp)
GO(gtk_offscreen_window_get_pixbuf, pFp)
GO(gtk_offscreen_window_get_pixmap, pFp) // Warning: failed to confirm
GO(gtk_offscreen_window_get_type, LFv)
GO(gtk_offscreen_window_new, pFv)
GO(gtk_old_editable_changed, vFp) // Warning: failed to confirm
GO(gtk_old_editable_claim_selection, vFpiu) // Warning: failed to confirm
GO(gtk_old_editable_get_type, LFv) // Warning: failed to confirm
GO(gtk_option_menu_get_history, iFp) // Warning: failed to confirm
GO(gtk_option_menu_get_menu, pFp) // Warning: failed to confirm
GO(gtk_option_menu_get_type, LFv) // Warning: failed to confirm
GO(gtk_option_menu_new, pFv) // Warning: failed to confirm
GO(gtk_option_menu_remove_menu, vFp) // Warning: failed to confirm
GO(gtk_option_menu_set_history, vFpu) // Warning: failed to confirm
GO(gtk_option_menu_set_menu, vFpp) // Warning: failed to confirm
GO(gtk_orientable_get_orientation, uFp)
GO(gtk_orientable_get_type, LFv)
GO(gtk_orientable_set_orientation, vFpu)
GO(gtk_orientation_get_type, LFv)
GO(gtk_overlay_add_overlay, vFpp)
GO(gtk_overlay_get_type, LFv)
GO(gtk_pack_direction_get_type, LFv)
GO(gtk_pack_type_get_type, LFv)
GO(gtk_page_orientation_get_type, LFv)
GO(gtk_page_set_get_type, LFv)
GO(gtk_page_setup_copy, pFp)
GO(gtk_page_setup_get_bottom_margin, dFpu)
GO(gtk_page_setup_get_left_margin, dFpu)
GO(gtk_page_setup_get_orientation, uFp)
GO(gtk_page_setup_get_page_height, dFpu)
GO(gtk_page_setup_get_page_width, dFpu)
GO(gtk_page_setup_get_paper_height, dFpu)
GO(gtk_page_setup_get_paper_size, pFp)
GO(gtk_page_setup_get_paper_width, dFpu)
GO(gtk_page_setup_get_right_margin, dFpu)
GO(gtk_page_setup_get_top_margin, dFpu)
GO(gtk_page_setup_get_type, LFv)
GO(gtk_page_setup_load_file, iFppp)
GO(gtk_page_setup_load_key_file, iFpppp)
GO(gtk_page_setup_new, pFv)
GO(gtk_page_setup_new_from_file, pFpp)
GO(gtk_page_setup_new_from_key_file, pFppp)
GO(gtk_page_setup_set_bottom_margin, vFpdu)
GO(gtk_page_setup_set_left_margin, vFpdu)
GO(gtk_page_setup_set_orientation, vFpu)
GO(gtk_page_setup_set_paper_size, vFpp)
GO(gtk_page_setup_set_paper_size_and_default_margins, vFpp)
GO(gtk_page_setup_set_right_margin, vFpdu)
GO(gtk_page_setup_set_top_margin, vFpdu)
GO(gtk_page_setup_to_file, iFppp)
GO(gtk_page_setup_to_key_file, vFppp)
//GO(gtk_page_setup_unix_dialog_get_page_setup, 
//GO(gtk_page_setup_unix_dialog_get_print_settings, 
GO(gtk_page_setup_unix_dialog_get_type, LFv) // Warning: failed to confirm
//GO(gtk_page_setup_unix_dialog_new, 
//GO(gtk_page_setup_unix_dialog_set_page_setup, 
//GO(gtk_page_setup_unix_dialog_set_print_settings, 
GO(gtk_paint_arrow, vFppuuppuiiiii)
GO(gtk_paint_box, vFppuuppiiii)
GO(gtk_paint_box_gap, vFppuuppiiiiuii)
GO(gtk_paint_check, vFppuuppiiii)
GO(gtk_paint_diamond, vFppuuppiiii)
GO(gtk_paint_expander, vFppuppiiu)
GO(gtk_paint_extension, vFppuuppiiiiu)
GO(gtk_paint_flat_box, vFppuuppiiii)
GO(gtk_paint_focus, vFppuppiiii)
GO(gtk_paint_handle, vFppuuppiiiiu)
GO(gtk_paint_hline, vFppuppiii)
GO(gtk_paint_layout, vFppuippiip)
GO(gtk_paint_option, vFppuuppiiii)
GO(gtk_paint_polygon, vFppiippppii) // Warning: failed to confirm
GO(gtk_paint_resize_grip, vFppuppuiiii)
GO(gtk_paint_shadow, vFppuuppiiii)
GO(gtk_paint_shadow_gap, vFppuuppiiiiuii)
GO(gtk_paint_slider, vFppuuppiiiiu)
GO(gtk_paint_spinner, vFppuppuiiii)
GO(gtk_paint_string, vFppipppiip) // Warning: failed to confirm
GO(gtk_paint_tab, vFppuuppiiii)
GO(gtk_paint_vline, vFppuppiii)
GO(gtk_paned_add1, vFpp)
GO(gtk_paned_add2, vFpp)
GO(gtk_paned_compute_position, vFpiii) // Warning: failed to confirm
GO(gtk_paned_get_child1, pFp)
GO(gtk_paned_get_child2, pFp)
GO(gtk_paned_get_handle_window, pFp)
GO(gtk_paned_get_position, iFp)
GO(gtk_paned_get_type, LFv)
GO(gtk_paned_new, pFu)
GO(gtk_paned_pack1, vFppii)
GO(gtk_paned_pack2, vFppii)
GO(gtk_paned_set_position, vFpi)
GO(gtk_paper_size_copy, pFp)
GO(gtk_paper_size_free, vFp)
GO(gtk_paper_size_get_default, pFv)
GO(gtk_paper_size_get_default_bottom_margin, dFpu)
GO(gtk_paper_size_get_default_left_margin, dFpu)
GO(gtk_paper_size_get_default_right_margin, dFpu)
GO(gtk_paper_size_get_default_top_margin, dFpu)
GO(gtk_paper_size_get_display_name, pFp)
GO(gtk_paper_size_get_height, dFpu)
GO(gtk_paper_size_get_name, pFp)
GO(gtk_paper_size_get_paper_sizes, pFi)
GO(gtk_paper_size_get_ppd_name, pFp)
GO(gtk_paper_size_get_type, LFv)
GO(gtk_paper_size_get_width, dFpu)
GO(gtk_paper_size_is_custom, iFp)
GO(gtk_paper_size_is_equal, iFpp)
GO(gtk_paper_size_new, pFp)
GO(gtk_paper_size_new_custom, pFppddu)
GO(gtk_paper_size_new_from_key_file, pFppp)
GO(gtk_paper_size_new_from_ppd, pFppdd)
GO(gtk_paper_size_set_size, vFpddu)
GO(gtk_paper_size_to_key_file, vFppp)
GO(gtk_parse_args, iFpp)
GO(gtk_path_bar_get_type, LFv) // Warning: failed to confirm
GO(gtk_path_priority_type_get_type, LFv)
GO(gtk_path_type_get_type, LFv)
GO(gtk_pixmap_get, vFppp) // Warning: failed to confirm
GO(gtk_pixmap_get_type, LFv) // Warning: failed to confirm
GO(gtk_pixmap_new, pFpp) // Warning: failed to confirm
GO(gtk_pixmap_set, vFppp) // Warning: failed to confirm
GO(gtk_pixmap_set_build_insensitive, vFpi) // Warning: failed to confirm
GO(gtk_plug_construct, vFpp) // Warning: failed to confirm
GO(gtk_plug_construct_for_display, vFppp) // Warning: failed to confirm
GO(gtk_plug_get_embedded, iFp) // Warning: failed to confirm
GO(gtk_plug_get_id, pFp) // Warning: failed to confirm
GO(gtk_plug_get_socket_window, pFp) // Warning: failed to confirm
GO(gtk_plug_get_type, LFv) // Warning: failed to confirm
GO(gtk_plug_new, pFp) // Warning: failed to confirm
GO(gtk_plug_new_for_display, pFpp) // Warning: failed to confirm
GO(gtk_policy_type_get_type, LFv)
GO(gtk_popover_get_type, LFv)
GO(gtk_position_type_get_type, LFv)
//GO(gtk_preview_draw_row, 
//GO(gtk_preview_get_cmap, 
//GO(gtk_preview_get_info, 
GO(gtk_preview_get_type, LFv) // Warning: failed to confirm
//GO(gtk_preview_get_visual, 
//GO(gtk_preview_new, 
//GO(gtk_preview_put, 
//GO(gtk_preview_reset, 
//GO(gtk_preview_set_color_cube, 
//GO(gtk_preview_set_dither, 
//GO(gtk_preview_set_expand, 
//GO(gtk_preview_set_gamma, 
//GO(gtk_preview_set_install_cmap, 
//GO(gtk_preview_set_reserved, 
//GO(gtk_preview_size, 
GO(gtk_preview_type_get_type, LFv) // Warning: failed to confirm
//GO(gtk_preview_uninit, 
//GO(gtk_print_backend_add_printer, 
//GO(gtk_print_backend_destroy, 
//GO(gtk_print_backend_error_quark, 
//GO(gtk_print_backend_find_printer, 
//GO(gtk_print_backend_get_printer_list, 
GO(gtk_print_backend_get_type, LFv) // Warning: failed to confirm
//GO(gtk_print_backend_load_modules, 
//GO(gtk_print_backend_printer_list_is_done, 
//GO(gtk_print_backend_print_stream, 
//GO(gtk_print_backend_remove_printer, 
//GO(gtk_print_backend_set_list_done, 
//GO(gtk_print_backend_set_password, 
GO(gtk_print_capabilities_get_type, LFv) // Warning: failed to confirm
GO(gtk_print_context_create_pango_context, pFp)
GO(gtk_print_context_create_pango_layout, pFp)
GO(gtk_print_context_get_cairo_context, pFp)
GO(gtk_print_context_get_dpi_x, dFp)
GO(gtk_print_context_get_dpi_y, dFp)
GO(gtk_print_context_get_hard_margins, iFppppp)
GO(gtk_print_context_get_height, dFp)
GO(gtk_print_context_get_page_setup, pFp)
GO(gtk_print_context_get_pango_fontmap, pFp)
GO(gtk_print_context_get_type, LFv)
GO(gtk_print_context_get_width, dFp)
GO(gtk_print_context_set_cairo_context, vFppdd)
GO(gtk_print_duplex_get_type, LFv)
//GO(gtk_printer_accepts_pdf, 
//GO(gtk_printer_accepts_ps, 
//GO(gtk_printer_compare, 
//GO(gtk_printer_get_backend, 
//GO(gtk_printer_get_capabilities, 
GO(gtk_printer_get_default_page_size, pFp) // Warning: failed to confirm
//GO(gtk_printer_get_description, 
//GO(gtk_printer_get_hard_margins, 
//GO(gtk_printer_get_icon_name, 
//GO(gtk_printer_get_job_count, 
//GO(gtk_printer_get_location, 
GO(gtk_printer_get_name, pFp) // Warning: failed to confirm
//GO(gtk_printer_get_state_message, 
GO(gtk_printer_get_type, LFv) // Warning: failed to confirm
//GO(gtk_printer_has_details, 
//GO(gtk_printer_is_accepting_jobs, 
//GO(gtk_printer_is_active, 
GO(gtk_printer_is_default, iFp) // Warning: failed to confirm
//GO(gtk_printer_is_new, 
//GO(gtk_printer_is_paused, 
//GO(gtk_printer_is_virtual, 
//GO(gtk_printer_list_papers, 
//GO(gtk_printer_new, 
//GO(gtk_printer_option_allocate_choices, 
//GO(gtk_printer_option_choices_from_array, 
//GO(gtk_printer_option_clear_has_conflict, 
//GO(gtk_printer_option_get_activates_default, 
GO(gtk_printer_option_get_type, LFv) // Warning: failed to confirm
//GO(gtk_printer_option_has_choice, 
//GO(gtk_printer_option_new, 
//GO(gtk_printer_option_set, 
//GO(gtk_printer_option_set_activates_default, 
//GO(gtk_printer_option_set_add, 
//GO(gtk_printer_option_set_boolean, 
//GO(gtk_printer_option_set_clear_conflicts, 
//GO(gtk_printer_option_set_foreach, 
//GO(gtk_printer_option_set_foreach_in_group, 
//GO(gtk_printer_option_set_get_groups, 
GO(gtk_printer_option_set_get_type, LFv) // Warning: failed to confirm
//GO(gtk_printer_option_set_has_conflict, 
//GO(gtk_printer_option_set_lookup, 
//GO(gtk_printer_option_set_new, 
//GO(gtk_printer_option_set_remove, 
//GO(gtk_printer_option_widget_get_external_label, 
GO(gtk_printer_option_widget_get_type, LFv) // Warning: failed to confirm
//GO(gtk_printer_option_widget_get_value, 
//GO(gtk_printer_option_widget_has_external_label, 
//GO(gtk_printer_option_widget_new, 
//GO(gtk_printer_option_widget_set_source, 
//GO(gtk_printer_request_details, 
GO(gtk_print_error_get_type, LFv)
GO(gtk_print_error_quark, uFv)
//GO(gtk_printer_set_accepts_pdf, 
//GO(gtk_printer_set_accepts_ps, 
//GO(gtk_printer_set_description, 
//GO(gtk_printer_set_has_details, 
//GO(gtk_printer_set_icon_name, 
//GO(gtk_printer_set_is_accepting_jobs, 
//GO(gtk_printer_set_is_active, 
//GO(gtk_printer_set_is_default, 
//GO(gtk_printer_set_is_new, 
//GO(gtk_printer_set_is_paused, 
//GO(gtk_printer_set_job_count, 
//GO(gtk_printer_set_location, 
//GO(gtk_printer_set_state_message, 
//GO(gtk_print_job_get_printer, 
//GO(gtk_print_job_get_settings, 
//GO(gtk_print_job_get_status, 
//GO(gtk_print_job_get_surface, 
//GO(gtk_print_job_get_title, 
//GO(gtk_print_job_get_track_print_status, 
GO(gtk_print_job_get_type, LFv) // Warning: failed to confirm
GO(gtk_print_job_new, pFpppp) // Warning: failed to confirm
GOM(gtk_print_job_send, vFEpppp) // Warning: failed to confirm
GO(gtk_print_job_set_source_file, iFppp) // Warning: failed to confirm
//GO(gtk_print_job_set_status, 
//GO(gtk_print_job_set_track_print_status, 
GO(gtk_print_operation_action_get_type, LFv)
GO(gtk_print_operation_cancel, vFp)
GO(gtk_print_operation_draw_page_finish, vFp)
GO(gtk_print_operation_get_default_page_setup, pFp)
GO(gtk_print_operation_get_embed_page_setup, iFp)
GO(gtk_print_operation_get_error, vFpp)
GO(gtk_print_operation_get_has_selection, iFp)
GO(gtk_print_operation_get_n_pages_to_print, iFp)
GO(gtk_print_operation_get_print_settings, pFp)
GO(gtk_print_operation_get_status, uFp)
GO(gtk_print_operation_get_status_string, pFp)
GO(gtk_print_operation_get_support_selection, iFp)
GO(gtk_print_operation_get_type, LFv)
GO(gtk_print_operation_is_finished, iFp)
GO(gtk_print_operation_new, pFv)
GO(gtk_print_operation_preview_end_preview, vFp)
GO(gtk_print_operation_preview_get_type, LFv)
GO(gtk_print_operation_preview_is_selected, iFpi)
GO(gtk_print_operation_preview_render_page, vFpi)
GO(gtk_print_operation_result_get_type, LFv)
GO(gtk_print_operation_run, uFpupp)
GO(gtk_print_operation_set_allow_async, vFpi)
GO(gtk_print_operation_set_current_page, vFpi)
GO(gtk_print_operation_set_custom_tab_label, vFpp)
GO(gtk_print_operation_set_default_page_setup, vFpp)
GO(gtk_print_operation_set_defer_drawing, vFp)
GO(gtk_print_operation_set_embed_page_setup, vFpi)
GO(gtk_print_operation_set_export_filename, vFpp)
GO(gtk_print_operation_set_has_selection, vFpi)
GO(gtk_print_operation_set_job_name, vFpp)
GO(gtk_print_operation_set_n_pages, vFpi)
GO(gtk_print_operation_set_print_settings, vFpp)
GO(gtk_print_operation_set_show_progress, vFpi)
GO(gtk_print_operation_set_support_selection, vFpi)
GO(gtk_print_operation_set_track_print_status, vFpi)
GO(gtk_print_operation_set_unit, vFpu)
GO(gtk_print_operation_set_use_full_page, vFpi)
GO(gtk_print_pages_get_type, LFv)
GO(gtk_print_quality_get_type, LFv)
GO(gtk_print_run_page_setup_dialog, pFppp)
//GOM(gtk_print_run_page_setup_dialog_async, vFppppp)
GO(gtk_print_settings_copy, pFp)
//GOM(gtk_print_settings_foreach, vFppp)
GO(gtk_print_settings_get, pFpp)
GO(gtk_print_settings_get_bool, iFpp)
GO(gtk_print_settings_get_collate, iFp)
GO(gtk_print_settings_get_default_source, pFp)
GO(gtk_print_settings_get_dither, pFp)
GO(gtk_print_settings_get_double, dFpp)
GO(gtk_print_settings_get_double_with_default, dFppd)
GO(gtk_print_settings_get_duplex, uFp)
GO(gtk_print_settings_get_finishings, pFp)
GO(gtk_print_settings_get_int, iFpp)
GO(gtk_print_settings_get_int_with_default, iFppi)
GO(gtk_print_settings_get_length, dFppu)
GO(gtk_print_settings_get_media_type, pFp)
GO(gtk_print_settings_get_n_copies, iFp)
GO(gtk_print_settings_get_number_up, iFp)
GO(gtk_print_settings_get_number_up_layout, uFp)
GO(gtk_print_settings_get_orientation, uFp)
GO(gtk_print_settings_get_output_bin, pFp)
GO(gtk_print_settings_get_page_ranges, pFpp)
GO(gtk_print_settings_get_page_set, uFp)
GO(gtk_print_settings_get_paper_height, dFpu)
GO(gtk_print_settings_get_paper_size, pFp)
GO(gtk_print_settings_get_paper_width, dFpu)
GO(gtk_print_settings_get_printer, pFp)
GO(gtk_print_settings_get_printer_lpi, dFp)
GO(gtk_print_settings_get_print_pages, uFp)
GO(gtk_print_settings_get_quality, uFp)
GO(gtk_print_settings_get_resolution, iFp)
GO(gtk_print_settings_get_resolution_x, iFp)
GO(gtk_print_settings_get_resolution_y, iFp)
GO(gtk_print_settings_get_reverse, iFp)
GO(gtk_print_settings_get_scale, dFp)
GO(gtk_print_settings_get_type, LFv)
GO(gtk_print_settings_get_use_color, iFp)
GO(gtk_print_settings_has_key, iFpp)
GO(gtk_print_settings_load_file, iFppp)
GO(gtk_print_settings_load_key_file, iFpppp)
GO(gtk_print_settings_new, pFv)
GO(gtk_print_settings_new_from_file, pFpp)
GO(gtk_print_settings_new_from_key_file, pFppp)
GO(gtk_print_settings_set, vFppp)
GO(gtk_print_settings_set_bool, vFppi)
GO(gtk_print_settings_set_collate, vFpi)
GO(gtk_print_settings_set_default_source, vFpp)
GO(gtk_print_settings_set_dither, vFpp)
GO(gtk_print_settings_set_double, vFppd)
GO(gtk_print_settings_set_duplex, vFpu)
GO(gtk_print_settings_set_finishings, vFpp)
GO(gtk_print_settings_set_int, vFppi)
GO(gtk_print_settings_set_length, vFppdu)
GO(gtk_print_settings_set_media_type, vFpp)
GO(gtk_print_settings_set_n_copies, vFpi)
GO(gtk_print_settings_set_number_up, vFpi)
GO(gtk_print_settings_set_number_up_layout, vFpu)
GO(gtk_print_settings_set_orientation, vFpu)
GO(gtk_print_settings_set_output_bin, vFpp)
GO(gtk_print_settings_set_page_ranges, vFppi)
GO(gtk_print_settings_set_page_set, vFpu)
GO(gtk_print_settings_set_paper_height, vFpdu)
GO(gtk_print_settings_set_paper_size, vFpp)
GO(gtk_print_settings_set_paper_width, vFpdu)
GO(gtk_print_settings_set_printer, vFpp)
GO(gtk_print_settings_set_printer_lpi, vFpd)
GO(gtk_print_settings_set_print_pages, vFpu)
GO(gtk_print_settings_set_quality, vFpu)
GO(gtk_print_settings_set_resolution, vFpi)
GO(gtk_print_settings_set_resolution_xy, vFpii)
GO(gtk_print_settings_set_reverse, vFpi)
GO(gtk_print_settings_set_scale, vFpd)
GO(gtk_print_settings_set_use_color, vFpi)
GO(gtk_print_settings_to_file, iFppp)
GO(gtk_print_settings_to_key_file, vFppp)
GO(gtk_print_settings_unset, vFpp)
GO(gtk_print_status_get_type, LFv)
//GO(gtk_print_unix_dialog_add_custom_tab, 
//GO(gtk_print_unix_dialog_get_current_page, 
//GO(gtk_print_unix_dialog_get_embed_page_setup, 
//GO(gtk_print_unix_dialog_get_has_selection, 
//GO(gtk_print_unix_dialog_get_manual_capabilities, 
GO(gtk_print_unix_dialog_get_page_setup, pFp) // Warning: failed to confirm
//GO(gtk_print_unix_dialog_get_page_setup_set, 
GO(gtk_print_unix_dialog_get_selected_printer, pFp) // Warning: failed to confirm
GO(gtk_print_unix_dialog_get_settings, pFp) // Warning: failed to confirm
//GO(gtk_print_unix_dialog_get_support_selection, 
GO(gtk_print_unix_dialog_get_type, LFv) // Warning: failed to confirm
GO(gtk_print_unix_dialog_new, pFpp) // Warning: failed to confirm
//GO(gtk_print_unix_dialog_set_current_page, 
GO(gtk_print_unix_dialog_set_embed_page_setup, vFpi) // Warning: failed to confirm
GO(gtk_print_unix_dialog_set_has_selection, vFpi) // Warning: failed to confirm
GO(gtk_print_unix_dialog_set_manual_capabilities, vFpi) // Warning: failed to confirm
//GO(gtk_print_unix_dialog_set_page_setup, 
GO(gtk_print_unix_dialog_set_settings, vFpp) // Warning: failed to confirm
GO(gtk_print_unix_dialog_set_support_selection, vFpi) // Warning: failed to confirm
GO(gtk_private_flags_get_type, LFv) // Warning: failed to confirm
GO(gtk_progress_bar_get_ellipsize, uFp)
GO(gtk_progress_bar_get_fraction, dFp)
GO(gtk_progress_bar_get_orientation, iFp) // Warning: failed to confirm
GO(gtk_progress_bar_get_pulse_step, dFp)
GO(gtk_progress_bar_get_text, pFp)
GO(gtk_progress_bar_get_type, LFv)
GO(gtk_progress_bar_new, pFv)
GO(gtk_progress_bar_new_with_adjustment, pFp) // Warning: failed to confirm
GO(gtk_progress_bar_orientation_get_type, LFv) // Warning: failed to confirm
GO(gtk_progress_bar_pulse, vFp)
GO(gtk_progress_bar_set_activity_blocks, vFpu) // Warning: failed to confirm
GO(gtk_progress_bar_set_activity_step, vFpu) // Warning: failed to confirm
GO(gtk_progress_bar_set_bar_style, vFpi) // Warning: failed to confirm
GO(gtk_progress_bar_set_discrete_blocks, vFpu) // Warning: failed to confirm
GO(gtk_progress_bar_set_ellipsize, vFpu)
GO(gtk_progress_bar_set_fraction, vFpd)
GO(gtk_progress_bar_set_orientation, vFpi) // Warning: failed to confirm
GO(gtk_progress_bar_set_pulse_step, vFpd)
GO(gtk_progress_bar_set_show_text, vFpi)
GO(gtk_progress_bar_set_text, vFpp)
GO(gtk_progress_bar_style_get_type, LFv) // Warning: failed to confirm
GO(gtk_progress_bar_update, vFpd) // Warning: failed to confirm
//GO(gtk_progress_configure, 
//GO(gtk_progress_get_current_percentage, 
//GO(gtk_progress_get_current_text, 
//GO(gtk_progress_get_percentage_from_value, 
//GO(gtk_progress_get_text_from_value, 
GO(gtk_progress_get_type, LFv) // Warning: failed to confirm
//GO(gtk_progress_get_value, 
//GO(gtk_progress_set_activity_mode, 
//GO(gtk_progress_set_adjustment, 
//GO(gtk_progress_set_format_string, 
//GO(gtk_progress_set_percentage, 
//GO(gtk_progress_set_show_text, 
//GO(gtk_progress_set_text_alignment, 
//GO(gtk_progress_set_value, 
GO(gtk_propagate_event, vFpp)
//GOM(gtk_quit_add, iFEuBp)
GO(gtk_quit_add_destroy, vFup) // Warning: failed to confirm
//GOM(gtk_quit_add_full, uFuBppB)
GO(gtk_quit_remove, vFu) // Warning: failed to confirm
GO(gtk_quit_remove_by_data, vFp) // Warning: failed to confirm
GO(gtk_radio_action_get_current_value, iFp)
GO(gtk_radio_action_get_group, pFp)
GO(gtk_radio_action_get_type, LFv)
GO(gtk_radio_action_new, pFppppi)
GO(gtk_radio_action_set_current_value, vFpi)
GO(gtk_radio_action_set_group, vFpp)
GO(gtk_radio_button_get_group, pFp)
GO(gtk_radio_button_get_type, LFv)
GO(gtk_radio_button_new, pFp)
GO(gtk_radio_button_new_from_widget, pFp)
GO(gtk_radio_button_new_with_label, pFpp)
GO(gtk_radio_button_new_with_label_from_widget, pFpp)
GO(gtk_radio_button_new_with_mnemonic, pFpp)
GO(gtk_radio_button_new_with_mnemonic_from_widget, pFpp)
GO(gtk_radio_button_set_group, vFpp)
GO(gtk_radio_menu_item_get_group, pFp)
GO(gtk_radio_menu_item_get_type, LFv)
GO(gtk_radio_menu_item_new, pFp)
GO(gtk_radio_menu_item_new_from_widget, pFp)
GO(gtk_radio_menu_item_new_with_label, pFpp)
GO(gtk_radio_menu_item_new_with_label_from_widget, pFpp)
GO(gtk_radio_menu_item_new_with_mnemonic, pFpp)
GO(gtk_radio_menu_item_new_with_mnemonic_from_widget, pFpp)
GO(gtk_radio_menu_item_set_group, vFpp)
GO(gtk_radio_tool_button_get_group, pFp)
GO(gtk_radio_tool_button_get_type, LFv)
GO(gtk_radio_tool_button_new, pFp)
GO(gtk_radio_tool_button_new_from_stock, pFpp)
GO(gtk_radio_tool_button_new_from_widget, pFp)
GO(gtk_radio_tool_button_new_with_stock_from_widget, pFpp)
GO(gtk_radio_tool_button_set_group, vFpp)
GO(gtk_range_get_adjustment, pFp)
GO(gtk_range_get_fill_level, dFp)
GO(gtk_range_get_flippable, iFp)
GO(gtk_range_get_inverted, iFp)
GO(gtk_range_get_lower_stepper_sensitivity, uFp)
GO(gtk_range_get_min_slider_size, iFp)
GO(gtk_range_get_range_rect, vFpp)
GO(gtk_range_get_restrict_to_fill_level, iFp)
GO(gtk_range_get_round_digits, iFp)
GO(gtk_range_get_show_fill_level, iFp)
GO(gtk_range_get_slider_range, vFppp)
GO(gtk_range_get_slider_size_fixed, iFp)
GO(gtk_range_get_type, LFv)
GO(gtk_range_get_update_policy, iFp) // Warning: failed to confirm
GO(gtk_range_get_upper_stepper_sensitivity, uFp)
GO(gtk_range_get_value, dFp)
GO(gtk_range_set_adjustment, vFpp)
GO(gtk_range_set_fill_level, vFpd)
GO(gtk_range_set_flippable, vFpi)
GO(gtk_range_set_increments, vFpdd)
GO(gtk_range_set_inverted, vFpi)
GO(gtk_range_set_lower_stepper_sensitivity, vFpu)
GO(gtk_range_set_min_slider_size, vFpi)
GO(gtk_range_set_range, vFpdd)
GO(gtk_range_set_restrict_to_fill_level, vFpi)
GO(gtk_range_set_round_digits, vFpi)
GO(gtk_range_set_show_fill_level, vFpi)
GO(gtk_range_set_slider_size_fixed, vFpi)
GO(gtk_range_set_update_policy, vFpi) // Warning: failed to confirm
GO(gtk_range_set_upper_stepper_sensitivity, vFpu)
GO(gtk_range_set_value, vFpd)
GO(gtk_rc_add_class_style, vFpp) // Warning: failed to confirm
GO(gtk_rc_add_default_file, vFp)
GO(gtk_rc_add_widget_class_style, vFpp) // Warning: failed to confirm
GO(gtk_rc_add_widget_name_style, vFpp) // Warning: failed to confirm
GO(gtk_rc_find_module_in_path, pFp)
GO(gtk_rc_find_pixmap_in_path, pFppp)
GO(gtk_rc_flags_get_type, LFv)
GO(gtk_rc_get_default_files, pFv)
GO(gtk_rc_get_im_module_file, pFv)
GO(gtk_rc_get_im_module_path, pFv)
GO(gtk_rc_get_module_dir, pFv)
GO(gtk_rc_get_style, pFp)
GO(gtk_rc_get_style_by_paths, pFpppL)
GO(gtk_rc_get_theme_dir, pFv)
GO(gtk_rc_parse, vFp)
//GOM(gtk_rc_parse_color, uFpp)
//GOM(gtk_rc_parse_color_full, uFppp)
//GOM(gtk_rc_parse_priority, uFpp)
//GOM(gtk_rc_parse_state, uFpp)
GO(gtk_rc_parse_string, vFp)
GO(gtk_rc_property_parse_border, iFppp)
GO(gtk_rc_property_parse_color, iFppp)
GO(gtk_rc_property_parse_enum, iFppp)
GO(gtk_rc_property_parse_flags, iFppp)
GO(gtk_rc_property_parse_requisition, iFppp)
GO(gtk_rc_reparse_all, iFv)
GO(gtk_rc_reparse_all_for_settings, iFpi)
GO(gtk_rc_reset_styles, vFp)
GO(gtk_rc_scanner_new, pFv)
GO(gtk_rc_set_default_files, vFp)
GO(gtk_rc_style_copy, pFp)
GO(gtk_rc_style_get_type, LFv)
GO(gtk_rc_style_new, pFv)
GO(gtk_rc_style_ref, vFp) // Warning: failed to confirm
GO(gtk_rc_style_unref, vFp) // Warning: failed to confirm
GO(gtk_rc_token_type_get_type, LFv)
GO(gtk_revealer_get_type, LFv)
GO(gtk_revealer_transition_type_get_type, LFv)
GO(gtk_recent_action_get_show_numbers, iFp)
GO(gtk_recent_action_get_type, LFv)
GO(gtk_recent_action_new, pFpppp)
GO(gtk_recent_action_new_for_manager, pFppppp)
GO(gtk_recent_action_set_show_numbers, vFpi)
GO(gtk_recent_chooser_add_filter, vFpp)
GO(gtk_recent_chooser_dialog_get_type, LFv)
//GOM(gtk_recent_chooser_dialog_new, pFpppV)
//GOM(gtk_recent_chooser_dialog_new_for_manager, pFppppV)
GO(gtk_recent_chooser_error_get_type, LFv)
GO(gtk_recent_chooser_error_quark, uFv)
GO(gtk_recent_chooser_get_current_item, pFp)
GO(gtk_recent_chooser_get_current_uri, pFp)
GO(gtk_recent_chooser_get_filter, pFp)
GO(gtk_recent_chooser_get_items, pFp)
GO(gtk_recent_chooser_get_limit, iFp)
GO(gtk_recent_chooser_get_local_only, iFp)
GO(gtk_recent_chooser_get_select_multiple, iFp)
GO(gtk_recent_chooser_get_show_icons, iFp)
GO(gtk_recent_chooser_get_show_not_found, iFp)
//GO(gtk_recent_chooser_get_show_numbers, 
GO(gtk_recent_chooser_get_show_private, iFp)
GO(gtk_recent_chooser_get_show_tips, iFp)
GO(gtk_recent_chooser_get_sort_type, uFp)
GO(gtk_recent_chooser_get_type, LFv)
GO(gtk_recent_chooser_get_uris, pFpp)
GO(gtk_recent_chooser_list_filters, pFp)
GO(gtk_recent_chooser_menu_get_show_numbers, iFp)
GO(gtk_recent_chooser_menu_get_type, LFv)
GO(gtk_recent_chooser_menu_new, pFv)
GO(gtk_recent_chooser_menu_new_for_manager, pFp)
GO(gtk_recent_chooser_menu_set_show_numbers, vFpi)
GO(gtk_recent_chooser_remove_filter, vFpp)
GO(gtk_recent_chooser_select_all, vFp)
GO(gtk_recent_chooser_select_uri, iFppp)
GO(gtk_recent_chooser_set_current_uri, iFppp)
GO(gtk_recent_chooser_set_filter, vFpp)
GO(gtk_recent_chooser_set_limit, vFpi)
GO(gtk_recent_chooser_set_local_only, vFpi)
GO(gtk_recent_chooser_set_select_multiple, vFpi)
GO(gtk_recent_chooser_set_show_icons, vFpi)
GO(gtk_recent_chooser_set_show_not_found, vFpi)
//GO(gtk_recent_chooser_set_show_numbers, 
GO(gtk_recent_chooser_set_show_private, vFpi)
GO(gtk_recent_chooser_set_show_tips, vFpi)
//GOM(gtk_recent_chooser_set_sort_func, vFpppp)
GO(gtk_recent_chooser_set_sort_type, vFpu)
GO(gtk_recent_chooser_unselect_all, vFp)
GO(gtk_recent_chooser_unselect_uri, vFpp)
GO(gtk_recent_chooser_widget_get_type, LFv)
GO(gtk_recent_chooser_widget_new, pFv)
GO(gtk_recent_chooser_widget_new_for_manager, pFp)
GO(gtk_recent_filter_add_age, vFpi)
GO(gtk_recent_filter_add_application, vFpp)
//GOM(gtk_recent_filter_add_custom, vFpuppp)
GO(gtk_recent_filter_add_group, vFpp)
GO(gtk_recent_filter_add_mime_type, vFpp)
GO(gtk_recent_filter_add_pattern, vFpp)
GO(gtk_recent_filter_add_pixbuf_formats, vFp)
GO(gtk_recent_filter_filter, iFpp)
GO(gtk_recent_filter_flags_get_type, LFv)
GO(gtk_recent_filter_get_name, pFp)
GO(gtk_recent_filter_get_needed, uFp)
GO(gtk_recent_filter_get_type, LFv)
GO(gtk_recent_filter_new, pFv)
GO(gtk_recent_filter_set_name, vFpp)
GO(gtk_recent_info_exists, iFp)
GO(gtk_recent_info_get_added, IFp)
GO(gtk_recent_info_get_age, iFp)
GO(gtk_recent_info_get_application_info, iFppppp)
GO(gtk_recent_info_get_applications, pFpp)
GO(gtk_recent_info_get_description, pFp)
GO(gtk_recent_info_get_display_name, pFp)
GO(gtk_recent_info_get_groups, pFpp)
GO(gtk_recent_info_get_icon, pFpi)
GO(gtk_recent_info_get_mime_type, pFp)
GO(gtk_recent_info_get_modified, IFp)
GO(gtk_recent_info_get_private_hint, iFp)
GO(gtk_recent_info_get_short_name, pFp)
GO(gtk_recent_info_get_type, LFv)
GO(gtk_recent_info_get_uri, pFp)
GO(gtk_recent_info_get_uri_display, pFp)
GO(gtk_recent_info_get_visited, IFp)
GO(gtk_recent_info_has_application, iFpp)
GO(gtk_recent_info_has_group, iFpp)
GO(gtk_recent_info_is_local, iFp)
GO(gtk_recent_info_last_application, pFp)
GO(gtk_recent_info_match, iFpp)
GO(gtk_recent_info_ref, pFp)
GO(gtk_recent_info_unref, vFp)
GO(gtk_recent_manager_add_full, iFppp)
GO(gtk_recent_manager_add_item, iFpp)
GO(gtk_recent_manager_error_get_type, LFv)
GO(gtk_recent_manager_error_quark, uFv)
GO(gtk_recent_manager_get_default, pFv)
//GO(gtk_recent_manager_get_for_screen, 
GO(gtk_recent_manager_get_items, pFp)
//GO(gtk_recent_manager_get_limit, 
GO(gtk_recent_manager_get_type, LFv)
GO(gtk_recent_manager_has_item, iFpp)
GO(gtk_recent_manager_lookup_item, pFppp)
GO(gtk_recent_manager_move_item, iFpppp)
GO(gtk_recent_manager_new, pFv)
GO(gtk_recent_manager_purge_items, iFpp)
GO(gtk_recent_manager_remove_item, iFppp)
//GO(gtk_recent_manager_set_limit, 
//GO(gtk_recent_manager_set_screen, 
GO(gtk_recent_sort_type_get_type, LFv)
GO(gtk_relief_style_get_type, LFv)
GO(gtk_render_activity, vFppdddd)
GO(gtk_render_arrow, vFppdddd)
GO(gtk_render_background, vFppdddd)
GO(gtk_render_background_get_clip, vFpddddp)
GO(gtk_render_check, vFppdddd)
GO(gtk_render_expander, vFppdddd)
GO(gtk_render_extension, vFppddddu)
GO(gtk_render_focus, vFppdddd)
GO(gtk_render_frame, vFppdddd)
GO(gtk_render_frame_gap, vFppddddudd)
GO(gtk_render_handle, vFppdddd)
GO(gtk_render_icon, vFpppdd)
GO(gtk_render_icon_pixbuf, pFppu)
GO(gtk_render_icon_surface, vFpppdd)
GO(gtk_render_insertion_cursor, vFppddpiu)
GO(gtk_render_layout, vFppddp)
GO(gtk_render_line, vFppdddd)
GO(gtk_render_option, vFppdddd)
GO(gtk_render_slider, vFppddddu)
GO(gtk_requisition_copy, pFp)
GO(gtk_requisition_free, vFp)
GO(gtk_requisition_get_type, LFv)
GO(gtk_resize_mode_get_type, LFv)
GO(gtk_response_type_get_type, LFv)
GO(gtk_rgb_to_hsv, vFdddppp)
//GO(gtk_ruler_draw_pos, 
//GO(gtk_ruler_draw_ticks, 
//GO(gtk_ruler_get_metric, 
//GO(gtk_ruler_get_range, 
GO(gtk_ruler_get_type, LFv) // Warning: failed to confirm
//GO(gtk_ruler_set_metric, 
//GO(gtk_ruler_set_range, 
GO(gtk_scale_add_mark, vFpdup)
GO(gtk_scale_button_get_adjustment, pFp)
GO(gtk_scale_button_get_minus_button, pFp)
//GO(gtk_scale_button_get_orientation, 
GO(gtk_scale_button_get_plus_button, pFp)
GO(gtk_scale_button_get_popup, pFp)
GO(gtk_scale_button_get_type, LFv)
GO(gtk_scale_button_get_value, dFp)
GO(gtk_scale_button_new, pFudddp)
GO(gtk_scale_button_set_adjustment, vFpp)
GO(gtk_scale_button_set_icons, vFpp)
//GO(gtk_scale_button_set_orientation, 
GO(gtk_scale_button_set_value, vFpd)
GO(gtk_scale_clear_marks, vFp)
GO(gtk_scale_get_digits, iFp)
GO(gtk_scale_get_draw_value, iFp)
GO(gtk_scale_get_layout, pFp)
GO(gtk_scale_get_layout_offsets, vFppp)
GO(gtk_scale_get_type, LFv)
GO(gtk_scale_get_value_pos, uFp)
GO(gtk_scale_new, pFup)
GO(gtk_scale_set_digits, vFpi)
GO(gtk_scale_set_draw_value, vFpi)
GO(gtk_scale_set_value_pos, vFpu)
GO(gtk_scrollable_get_type, LFv)
GO(gtk_scrollbar_get_type, LFv)
GO(gtk_scrollbar_new, pFup)
GO(gtk_scrolled_window_add_with_viewport, vFpp)
GO(gtk_scrolled_window_get_hadjustment, pFp)
GO(gtk_scrolled_window_get_hscrollbar, pFp)
GO(gtk_scrolled_window_get_placement, uFp)
GO(gtk_scrolled_window_get_policy, vFppp)
GO(gtk_scrolled_window_get_shadow_type, uFp)
GO(gtk_scrolled_window_get_type, LFv)
GO(gtk_scrolled_window_get_vadjustment, pFp)
GO(gtk_scrolled_window_get_vscrollbar, pFp)
GO(gtk_scrolled_window_new, pFpp)
GO(gtk_scrolled_window_set_hadjustment, vFpp)
GO(gtk_scrolled_window_set_placement, vFpu)
GO(gtk_scrolled_window_set_policy, vFpuu)
GO(gtk_scrolled_window_set_shadow_type, vFpu)
GO(gtk_scrolled_window_set_vadjustment, vFpp)
GO(gtk_scrolled_window_unset_placement, vFp)
GO(gtk_scroll_step_get_type, LFv)
GO(gtk_scroll_type_get_type, LFv)
GO(gtk_search_bar_get_type, LFv)
GO(gtk_search_entry_get_type, LFv)
GO(gtk_selection_add_target, vFpppu)
GO(gtk_selection_add_targets, vFpppu)
GO(gtk_selection_clear, iFpp) // Warning: failed to confirm
GO(gtk_selection_clear_targets, vFpp)
GO(gtk_selection_convert, iFpppu)
GO(gtk_selection_data_copy, pFp)
GO(gtk_selection_data_free, vFp)
GO(gtk_selection_data_get_data, pFp)
GO(gtk_selection_data_get_data_type, pFp)
GO(gtk_selection_data_get_display, pFp)
GO(gtk_selection_data_get_format, iFp)
GO(gtk_selection_data_get_length, iFp)
GO(gtk_selection_data_get_pixbuf, pFp)
GO(gtk_selection_data_get_selection, pFp)
GO(gtk_selection_data_get_target, pFp)
GO(gtk_selection_data_get_targets, iFppp)
GO(gtk_selection_data_get_text, pFp)
GO(gtk_selection_data_get_type, LFv)
GO(gtk_selection_data_get_uris, pFp)
GO(gtk_selection_data_set, vFppipi)
GO(gtk_selection_data_set_pixbuf, iFpp)
GO(gtk_selection_data_set_text, iFppi)
GO(gtk_selection_data_set_uris, iFpp)
GO(gtk_selection_data_targets_include_image, iFpi)
GO(gtk_selection_data_targets_include_rich_text, iFpp)
GO(gtk_selection_data_targets_include_text, iFp)
GO(gtk_selection_data_targets_include_uri, iFp)
GO(gtk_selection_mode_get_type, LFv)
GO(gtk_selection_owner_set, iFppu)
GO(gtk_selection_owner_set_for_display, iFpppu)
GO(gtk_selection_remove_all, vFp)
GO(gtk_sensitivity_type_get_type, LFv)
GO(gtk_separator_get_type, LFv)
GO(gtk_separator_menu_item_get_type, LFv)
GO(gtk_separator_menu_item_new, pFv)
GO(gtk_separator_new, pFu)
GO(gtk_separator_tool_item_get_draw, iFp)
GO(gtk_separator_tool_item_get_type, LFv)
GO(gtk_separator_tool_item_new, pFv)
GO(gtk_separator_tool_item_set_draw, vFpi)
GO(gtk_set_locale, pFv) // Warning: failed to confirm
GO(gtk_settings_get_default, pFv)
GO(gtk_settings_get_for_screen, pFp)
GO(gtk_settings_get_type, LFv)
GO(gtk_settings_install_property, vFp)
//GOM(gtk_settings_install_property_parser, vFEpp)
GO(gtk_settings_set_double_property, vFppdp)
GO(gtk_settings_set_long_property, vFpplp)
GO(gtk_settings_set_property_value, vFppp)
GO(gtk_settings_set_string_property, vFpppp)
GO(gtk_shadow_type_get_type, LFv)
GO(gtk_show_about_dialog, vFpppppppppppppppppppppppp)   //vaarg
GO(gtk_show_uri, iFppup)
GO(gtk_show_uri_on_window, iFppup)
GO(gtk_side_type_get_type, LFv) // Warning: failed to confirm
//GO(gtk_signal_compat_matched, 
GOM(gtk_signal_connect_full, LFEppppppii) // Warning: failed to confirm
//GO(gtk_signal_connect_object_while_alive, 
//GO(gtk_signal_connect_while_alive, 
//GO(gtk_signal_emit, 
//GO(gtk_signal_emit_by_name, 
//GO(gtk_signal_emit_stop_by_name, 
//GO(gtk_signal_emitv, 
//GO(gtk_signal_emitv_by_name, 
//GO(gtk_signal_new, 
//GO(gtk_signal_newv, 
GO(gtk_signal_run_type_get_type, LFv) // Warning: failed to confirm
GO(gtk_size_group_add_widget, vFpp)
GO(gtk_size_group_get_ignore_hidden, iFp)
GO(gtk_size_group_get_mode, uFp)
GO(gtk_size_group_get_type, LFv)
GO(gtk_size_group_get_widgets, pFp)
GO(gtk_size_group_mode_get_type, LFv)
GO(gtk_size_group_new, pFu)
GO(gtk_size_group_remove_widget, vFpp)
GO(gtk_size_group_set_ignore_hidden, vFpi)
GO(gtk_size_group_set_mode, vFpu)
GO(gtk_snapshot_new, pFv) // Warning: failed to confirm
GO(gtk_snapshot_free_to_node, pFp) // Warning: failed to confirm
GO(gtk_snapshot_render_background, vFppdddd) // Warning: failed to confirm
GO(gtk_socket_add_id, vFpp) // Warning: failed to confirm
GO(gtk_socket_get_id, pFp) // Warning: failed to confirm
GO(gtk_socket_get_plug_window, pFp) // Warning: failed to confirm
GO(gtk_socket_get_type, LFv) // Warning: failed to confirm
GO(gtk_socket_new, pFv) // Warning: failed to confirm
GO(gtk_socket_steal, vFpp) // Warning: failed to confirm
GO(gtk_sort_type_get_type, LFv)
GO(gtk_spin_button_configure, vFppdu)
GO(gtk_spin_button_get_adjustment, pFp)
GO(gtk_spin_button_get_digits, uFp)
GO(gtk_spin_button_get_increments, vFppp)
GO(gtk_spin_button_get_numeric, iFp)
GO(gtk_spin_button_get_range, vFppp)
GO(gtk_spin_button_get_snap_to_ticks, iFp)
GO(gtk_spin_button_get_type, LFv)
GO(gtk_spin_button_get_update_policy, uFp)
GO(gtk_spin_button_get_value, dFp)
GO(gtk_spin_button_get_value_as_int, iFp)
GO(gtk_spin_button_get_wrap, iFp)
GO(gtk_spin_button_new, pFpdu)
GO(gtk_spin_button_new_with_range, pFddd)
GO(gtk_spin_button_set_adjustment, vFpp)
GO(gtk_spin_button_set_digits, vFpu)
GO(gtk_spin_button_set_increments, vFpdd)
GO(gtk_spin_button_set_numeric, vFpi)
GO(gtk_spin_button_set_range, vFpdd)
GO(gtk_spin_button_set_snap_to_ticks, vFpi)
GO(gtk_spin_button_set_update_policy, vFpu)
GO(gtk_spin_button_set_value, vFpd)
GO(gtk_spin_button_set_wrap, vFpi)
GO(gtk_spin_button_spin, vFpud)
GO(gtk_spin_button_update, vFp)
GO(gtk_spin_button_update_policy_get_type, LFv)
GO(gtk_spinner_get_type, LFv)
GO(gtk_spinner_new, pFv)
GO(gtk_spinner_start, vFp)
GO(gtk_spinner_stop, vFp)
GO(gtk_spin_type_get_type, LFv)
GO(gtk_stack_get_type, LFv)
GO(gtk_stack_switcher_get_type, LFv)
GO(gtk_stack_transition_type_get_type, LFv)
GO(gtk_state_flags_get_type, LFv)
GO(gtk_state_type_get_type, LFv)
GO(gtk_statusbar_get_context_id, uFpp)
GO(gtk_statusbar_get_has_resize_grip, iFp) // Warning: failed to confirm
GO(gtk_statusbar_get_message_area, pFp)
GO(gtk_statusbar_get_type, LFv)
GO(gtk_statusbar_new, pFv)
GO(gtk_statusbar_pop, vFpu)
GO(gtk_statusbar_push, uFpup)
GO(gtk_statusbar_remove, vFpuu)
GO(gtk_statusbar_remove_all, vFpu)
GO(gtk_statusbar_set_has_resize_grip, vFpi) // Warning: failed to confirm
GO(gtk_status_icon_get_blinking, iFp) // Warning: failed to confirm
GO(gtk_status_icon_get_geometry, iFpppp)
GO(gtk_status_icon_get_gicon, pFp)
GO(gtk_status_icon_get_has_tooltip, iFp)
GO(gtk_status_icon_get_icon_name, pFp)
GO(gtk_status_icon_get_pixbuf, pFp)
GO(gtk_status_icon_get_screen, pFp)
GO(gtk_status_icon_get_size, iFp)
GO(gtk_status_icon_get_stock, pFp)
GO(gtk_status_icon_get_storage_type, uFp)
GO(gtk_status_icon_get_title, pFp)
GO(gtk_status_icon_get_tooltip_markup, pFp)
GO(gtk_status_icon_get_tooltip_text, pFp)
GO(gtk_status_icon_get_type, LFv)
GO(gtk_status_icon_get_visible, iFp)
GO(gtk_status_icon_get_x11_window_id, uFp)
GO(gtk_status_icon_is_embedded, iFp)
GO(gtk_status_icon_new, pFv)
GO(gtk_status_icon_new_from_file, pFp)
GO(gtk_status_icon_new_from_gicon, pFp)
GO(gtk_status_icon_new_from_icon_name, pFp)
GO(gtk_status_icon_new_from_pixbuf, pFp)
GO(gtk_status_icon_new_from_stock, pFp)
GO(gtk_status_icon_position_menu, vFppppp)
GO(gtk_status_icon_set_blinking, vFpi) // Warning: failed to confirm
GO(gtk_status_icon_set_from_file, vFpp)
GO(gtk_status_icon_set_from_gicon, vFpp)
GO(gtk_status_icon_set_from_icon_name, vFpp)
GO(gtk_status_icon_set_from_pixbuf, vFpp)
GO(gtk_status_icon_set_from_stock, vFpp)
GO(gtk_status_icon_set_has_tooltip, vFpi)
GO(gtk_status_icon_set_name, vFpp)
GO(gtk_status_icon_set_screen, vFpp)
GO(gtk_status_icon_set_title, vFpp)
GO(gtk_status_icon_set_tooltip, vFpp) // Warning: failed to confirm
GO(gtk_status_icon_set_tooltip_markup, vFpp)
GO(gtk_status_icon_set_tooltip_text, vFpp)
GO(gtk_status_icon_set_visible, vFpi)
GO(gtk_stock_add, vFpu)
GO(gtk_stock_add_static, vFpu)
GO(gtk_stock_item_copy, pFp)
GO(gtk_stock_item_free, vFp)
GO(gtk_stock_list_ids, pFv)
GO(gtk_stock_lookup, iFpp)
GOM(gtk_stock_set_translate_func, vFEpppp)
GO(gtk_style_apply_default_background, vFpppuiiii)
GO(gtk_style_attach, pFpp)
GO(gtk_style_context_add_class, vFpp)
GO(gtk_style_context_add_provider, vFppu)
GO(gtk_style_context_add_provider_for_display, vFppu) // Warning: failed to confirm
GO(gtk_style_context_add_provider_for_screen, vFppu)
GO(gtk_style_context_add_region, vFppu)
GO(gtk_style_context_cancel_animations, vFpp)
GOM(gtk_style_context_get, vFEpuV)
GO(gtk_style_context_get_border, vFpup)
GO(gtk_style_context_get_background_color, vFpup)
GO(gtk_style_context_get_border_color, vFpup)
GO(gtk_style_context_get_color, vFpup)
GO(gtk_style_context_get_direction, uFp)
GO(gtk_style_context_get_font, pFpu)
GO(gtk_style_context_get_junction_sides, uFp)
GO(gtk_style_context_get_margin, vFpup)
GO(gtk_style_context_get_padding, vFpup)
GO(gtk_style_context_get_parent, pFp)
GO(gtk_style_context_get_path, pFp)
GO(gtk_style_context_get_property, vFppup)
GO(gtk_style_context_get_frame_clock, pFp)
GO(gtk_style_context_get_scale, iFp)
GO(gtk_style_context_get_screen, pFp)
GO(gtk_style_context_get_section, pFpp)
GO(gtk_style_context_get_state, uFp)
GOM(gtk_style_context_get_style, vFpV)
GO(gtk_style_context_get_style_property, vFppp)
GOM(gtk_style_context_get_style_valist, vFEpA)
GOM(gtk_style_context_get_valist, vFEpuA)
GO(gtk_style_context_has_class, iFpp)
GO(gtk_style_context_has_region, iFppp)
GO(gtk_style_context_invalidate, vFp)
GO(gtk_style_context_list_classes, pFp)
GO(gtk_style_context_list_regions, pFp)
GO(gtk_style_context_lookup_color, iFppp)
GO(gtk_style_context_lookup_icon_set, pFpp)
GO(gtk_style_context_new, pFv)
GO(gtk_style_context_notify_state_change, vFpppui)
GO(gtk_style_context_pop_animatable_region, vFp)
GO(gtk_style_context_push_animatable_region, vFpp)
GO(gtk_style_context_restore, vFp)
GO(gtk_style_context_remove_class, vFpp)
GO(gtk_style_context_remove_provider, vFpp)
GO(gtk_style_context_remove_provider_for_display, vFpp) // Warning: failed to confirm
GO(gtk_style_context_remove_provider_for_screen, vFpp)
GO(gtk_style_context_remove_region, vFpp)
GO(gtk_style_context_reset_widgets, vFp)
GO(gtk_style_context_save, vFp)
GO(gtk_style_context_scroll_animations, vFppii)
GO(gtk_style_context_set_background, vFpp)
GO(gtk_style_context_set_direction, vFpu)
GO(gtk_style_context_set_frame_clock, vFpp)
GO(gtk_style_context_set_junction_sides, vFpu)
GO(gtk_style_context_set_parent, vFpp)
GO(gtk_style_context_set_path, vFpp)
GO(gtk_style_context_set_scale, vFpi)
GO(gtk_style_context_set_screen, vFpp)
GO(gtk_style_context_set_state, vFpu)
GO(gtk_style_context_state_is_running, iFpup)
GO(gtk_style_context_to_string, pFpu)
GO(gtk_style_copy, pFp)
GO(gtk_style_detach, vFp)
//GOM(gtk_style_get, vFpLpV)
GO(gtk_style_get_font, pFp)
GO(gtk_style_get_style_property, vFpLpp)
GO(gtk_style_get_type, LFv)
//GOM(gtk_style_get_valist, vFpLpA)
GO(gtk_style_lookup_color, iFppp)
GO(gtk_style_lookup_icon_set, pFpp)
GO(gtk_style_new, pFv)
GO(gtk_style_ref, pFp) // Warning: failed to confirm
GO(gtk_style_render_icon, pFppuuupp)
GO(gtk_style_set_background, vFppu)
GO(gtk_style_set_font, vFpp) // Warning: failed to confirm
GO(gtk_style_provider_get_type, LFv)
GO(gtk_style_unref, vFp) // Warning: failed to confirm
GO(gtk_submenu_direction_get_type, LFv) // Warning: failed to confirm
GO(gtk_submenu_placement_get_type, LFv) // Warning: failed to confirm
GO(gtk_switch_get_type, LFv)
GO(gtk_table_attach, vFppuuuuuuuu)
GO(gtk_table_attach_defaults, vFppuuuu)
GO(gtk_table_get_col_spacing, uFpu)
GO(gtk_table_get_default_col_spacing, uFp)
GO(gtk_table_get_default_row_spacing, uFp)
GO(gtk_table_get_homogeneous, iFp)
GO(gtk_table_get_row_spacing, uFpu)
GO(gtk_table_get_size, vFppp)
GO(gtk_table_get_type, LFv)
GO(gtk_table_new, pFuui)
GO(gtk_table_resize, vFpuu)
GO(gtk_table_set_col_spacing, vFpuu)
GO(gtk_table_set_col_spacings, vFpu)
GO(gtk_table_set_homogeneous, vFpi)
GO(gtk_table_set_row_spacing, vFpuu)
GO(gtk_table_set_row_spacings, vFpu)
GO(gtk_target_entry_get_type, LFv)
GO(gtk_target_flags_get_type, LFv)
GO(gtk_target_list_add, vFppuu)
GO(gtk_target_list_add_image_targets, vFpui)
GO(gtk_target_list_add_rich_text_targets, vFpuip)
GO(gtk_target_list_add_table, vFppu)
GO(gtk_target_list_add_text_targets, vFpu)
GO(gtk_target_list_add_uri_targets, vFpu)
GO(gtk_target_list_find, iFppp)
GO(gtk_target_list_get_type, LFv)
GO(gtk_target_list_new, pFpu)
GO(gtk_target_list_ref, pFp)
GO(gtk_target_list_remove, vFpp)
GO(gtk_target_list_unref, vFp)
GO(gtk_targets_include_image, iFpii)
GO(gtk_targets_include_rich_text, iFpip)
GO(gtk_targets_include_text, iFpi)
GO(gtk_targets_include_uri, iFpi)
GO(gtk_target_table_free, vFpi)
GO(gtk_target_table_new_from_list, pFpp)
GO(gtk_tearoff_menu_item_get_type, LFv)
GO(gtk_tearoff_menu_item_new, pFv)
GO(gtk_test_create_simple_window, pFpp)
//GOM(gtk_test_create_widget, pFLpV)
//GOM(gtk_test_display_button_window, pFppV)
GO(gtk_test_find_label, pFpp)
GO(gtk_test_find_sibling, pFpL)
GO(gtk_test_find_widget, pFppL)
//GOM(gtk_test_init, vFppV)
GO(gtk_test_list_all_types, pFp)
GO(gtk_test_register_all_types, vFv)
GO(gtk_test_slider_get_value, dFp)
GO(gtk_test_slider_set_perc, vFpd)
GO(gtk_test_spin_button_click, iFpui)
GO(gtk_test_text_get, pFp)
GO(gtk_test_text_set, vFpp)
GO(gtk_test_widget_click, iFpuu)
GO(gtk_test_widget_send_key, iFpuu)
GO(gtk_text_anchored_child_set_layout, vFpp) // Warning: failed to confirm
GO(gtk_text_attributes_copy, pFp)
GO(gtk_text_attributes_copy_values, vFpp)
GO(gtk_text_attributes_get_type, LFv)
GO(gtk_text_attributes_new, pFv)
GO(gtk_text_attributes_ref, pFp)
GO(gtk_text_attributes_unref, vFp)
GO(gtk_text_backward_delete, iFpu) // Warning: failed to confirm
GO(gtk_text_buffer_add_mark, vFppp)
GO(gtk_text_buffer_add_selection_clipboard, vFpp)
GO(gtk_text_buffer_apply_tag, vFpppp)
GO(gtk_text_buffer_apply_tag_by_name, vFpppp)
GO(gtk_text_buffer_backspace, iFppii)
GO(gtk_text_buffer_begin_user_action, vFp)
GO(gtk_text_buffer_copy_clipboard, vFpp)
GO(gtk_text_buffer_create_child_anchor, pFpp)
GO(gtk_text_buffer_create_mark, pFpppi)
GO(gtk_text_buffer_create_tag, pFppppppppppppppp) //vaarg after 3 p
GO(gtk_text_buffer_cut_clipboard, vFppi)
GO(gtk_text_buffer_delete, vFppp)
GO(gtk_text_buffer_delete_interactive, iFpppi)
GO(gtk_text_buffer_delete_mark, vFpp)
GO(gtk_text_buffer_delete_mark_by_name, vFpp)
GO(gtk_text_buffer_delete_selection, iFpii)
GO(gtk_text_buffer_deserialize, iFpppppLp)
GO(gtk_text_buffer_deserialize_get_can_create_tags, iFpp)
GO(gtk_text_buffer_deserialize_set_can_create_tags, vFppi)
GO(gtk_text_buffer_end_user_action, vFp)
GO(gtk_text_buffer_get_bounds, vFppp)
GO(gtk_text_buffer_get_char_count, iFp)
GO(gtk_text_buffer_get_copy_target_list, pFp)
GO(gtk_text_buffer_get_deserialize_formats, pFpp)
GO(gtk_text_buffer_get_end_iter, vFpp)
GO(gtk_text_buffer_get_has_selection, iFp)
GO(gtk_text_buffer_get_insert, pFp)
GO(gtk_text_buffer_get_iter_at_child_anchor, vFppp)
GO(gtk_text_buffer_get_iter_at_line, vFppi)
GO(gtk_text_buffer_get_iter_at_line_index, vFppii)
GO(gtk_text_buffer_get_iter_at_line_offset, vFppii)
GO(gtk_text_buffer_get_iter_at_mark, vFppp)
GO(gtk_text_buffer_get_iter_at_offset, vFppi)
GO(gtk_text_buffer_get_line_count, iFp)
GO(gtk_text_buffer_get_mark, pFpp)
GO(gtk_text_buffer_get_modified, iFp)
GO(gtk_text_buffer_get_paste_target_list, pFp)
GO(gtk_text_buffer_get_selection_bound, pFp)
GO(gtk_text_buffer_get_selection_bounds, iFppp)
GO(gtk_text_buffer_get_serialize_formats, pFpp)
GO(gtk_text_buffer_get_slice, pFpppi)
GO(gtk_text_buffer_get_start_iter, vFpp)
GO(gtk_text_buffer_get_tag_table, pFp)
GO(gtk_text_buffer_get_text, pFpppi)
GO(gtk_text_buffer_get_type, LFv)
GO(gtk_text_buffer_insert, vFpppi)
GO(gtk_text_buffer_insert_at_cursor, vFppi)
GO(gtk_text_buffer_insert_child_anchor, vFppp)
GO(gtk_text_buffer_insert_interactive, iFpppii)
GO(gtk_text_buffer_insert_interactive_at_cursor, iFppii)
GO(gtk_text_buffer_insert_pixbuf, vFppp)
GO(gtk_text_buffer_insert_range, vFpppp)
GO(gtk_text_buffer_insert_range_interactive, iFppppi)
GO(gtk_text_buffer_insert_with_tags, vFpppipppppppppppppp)
GO(gtk_text_buffer_insert_with_tags_by_name, vFpppippppppppppp)
GO(gtk_text_buffer_move_mark, vFppp)
GO(gtk_text_buffer_move_mark_by_name, vFppp)
GO(gtk_text_buffer_new, pFp)
GO(gtk_text_buffer_paste_clipboard, vFpppi)
GO(gtk_text_buffer_place_cursor, vFpp)
//GOM(gtk_text_buffer_register_deserialize_format, pFEppppp)
GO(gtk_text_buffer_register_deserialize_tagset, pFpp)
//GOM(gtk_text_buffer_register_serialize_format, pFppppp)
GO(gtk_text_buffer_register_serialize_tagset, pFpp)
GO(gtk_text_buffer_remove_all_tags, vFppp)
GO(gtk_text_buffer_remove_selection_clipboard, vFpp)
GO(gtk_text_buffer_remove_tag, vFpppp)
GO(gtk_text_buffer_remove_tag_by_name, vFpppp)
GO(gtk_text_buffer_select_range, vFppp)
GO(gtk_text_buffer_serialize, pFpppppp)
GO(gtk_text_buffer_set_modified, vFpi)
GO(gtk_text_buffer_set_text, vFppi)
GO(gtk_text_buffer_target_info_get_type, LFv)
GO(gtk_text_buffer_unregister_deserialize_format, vFpp)
GO(gtk_text_buffer_unregister_serialize_format, vFpp)
GO(gtk_text_byte_begins_utf8_char, iFp) // Warning: failed to confirm
GO(gtk_text_child_anchor_get_deleted, iFp)
GO(gtk_text_child_anchor_get_type, LFv)
GO(gtk_text_child_anchor_get_widgets, pFp)
GO(gtk_text_child_anchor_new, pFv)
GO(gtk_text_child_anchor_queue_resize, vFpp) // Warning: failed to confirm
GO(gtk_text_child_anchor_register_child, vFppp) // Warning: failed to confirm
GO(gtk_text_child_anchor_unregister_child, vFpp) // Warning: failed to confirm
GO(gtk_text_direction_get_type, LFv)
GO(gtk_text_forward_delete, iFpu) // Warning: failed to confirm
GO(gtk_text_freeze, vFp) // Warning: failed to confirm
GO(gtk_text_get_length, uFp) // Warning: failed to confirm
GO(gtk_text_get_point, uFp) // Warning: failed to confirm
GO(gtk_text_get_type, LFv) // Warning: failed to confirm
GO(gtk_text_insert, vFpppppi) // Warning: failed to confirm
GO(gtk_text_iter_backward_char, iFp)
GO(gtk_text_iter_backward_chars, iFpi)
GO(gtk_text_iter_backward_cursor_position, iFp)
GO(gtk_text_iter_backward_cursor_positions, iFpi)
GOM(gtk_text_iter_backward_find_char, iFEpppp)
GO(gtk_text_iter_backward_line, iFp)
GO(gtk_text_iter_backward_lines, iFpi)
GO(gtk_text_iter_backward_search, iFppuppp)
GO(gtk_text_iter_backward_sentence_start, iFp)
GO(gtk_text_iter_backward_sentence_starts, iFpi)
GO(gtk_text_iter_backward_to_tag_toggle, iFpp)
GO(gtk_text_iter_backward_visible_cursor_position, iFp)
GO(gtk_text_iter_backward_visible_cursor_positions, iFpi)
GO(gtk_text_iter_backward_visible_line, iFp)
GO(gtk_text_iter_backward_visible_lines, iFpi)
GO(gtk_text_iter_backward_visible_word_start, iFp)
GO(gtk_text_iter_backward_visible_word_starts, iFpi)
GO(gtk_text_iter_backward_word_start, iFp)
GO(gtk_text_iter_backward_word_starts, iFpi)
GO(gtk_text_iter_begins_tag, iFpp)
GO(gtk_text_iter_can_insert, iFpi)
GO(gtk_text_iter_compare, iFpp)
GO(gtk_text_iter_copy, pFp)
GO(gtk_text_iter_editable, iFpi)
GO(gtk_text_iter_ends_line, iFp)
GO(gtk_text_iter_ends_sentence, iFp)
GO(gtk_text_iter_ends_tag, iFpp)
GO(gtk_text_iter_ends_word, iFp)
GO(gtk_text_iter_equal, iFpp)
GO(gtk_text_iter_forward_char, iFp)
GO(gtk_text_iter_forward_chars, iFpi)
GO(gtk_text_iter_forward_cursor_position, iFp)
GO(gtk_text_iter_forward_cursor_positions, iFpi)
GOM(gtk_text_iter_forward_find_char, iFEpppp)
GO(gtk_text_iter_forward_line, iFp)
GO(gtk_text_iter_forward_lines, iFpi)
GO(gtk_text_iter_forward_search, iFppuppp)
GO(gtk_text_iter_forward_sentence_end, iFp)
GO(gtk_text_iter_forward_sentence_ends, iFpi)
GO(gtk_text_iter_forward_to_end, vFp)
GO(gtk_text_iter_forward_to_line_end, iFp)
GO(gtk_text_iter_forward_to_tag_toggle, iFpp)
GO(gtk_text_iter_forward_visible_cursor_position, iFp)
GO(gtk_text_iter_forward_visible_cursor_positions, iFpi)
GO(gtk_text_iter_forward_visible_line, iFp)
GO(gtk_text_iter_forward_visible_lines, iFpi)
GO(gtk_text_iter_forward_visible_word_end, iFp)
GO(gtk_text_iter_forward_visible_word_ends, iFpi)
GO(gtk_text_iter_forward_word_end, iFp)
GO(gtk_text_iter_forward_word_ends, iFpi)
GO(gtk_text_iter_free, vFp)
GO(gtk_text_iter_get_attributes, iFpp)
GO(gtk_text_iter_get_buffer, pFp)
GO(gtk_text_iter_get_bytes_in_line, iFp)
GO(gtk_text_iter_get_char, uFp)
GO(gtk_text_iter_get_chars_in_line, iFp)
GO(gtk_text_iter_get_child_anchor, pFp)
GO(gtk_text_iter_get_language, pFp)
GO(gtk_text_iter_get_line, iFp)
GO(gtk_text_iter_get_line_index, iFp)
GO(gtk_text_iter_get_line_offset, iFp)
GO(gtk_text_iter_get_marks, pFp)
GO(gtk_text_iter_get_offset, iFp)
GO(gtk_text_iter_get_pixbuf, pFp)
GO(gtk_text_iter_get_slice, pFpp)
GO(gtk_text_iter_get_tags, pFp)
GO(gtk_text_iter_get_text, pFpp)
GO(gtk_text_iter_get_toggled_tags, pFpi)
GO(gtk_text_iter_get_type, LFv)
GO(gtk_text_iter_get_visible_line_index, iFp)
GO(gtk_text_iter_get_visible_line_offset, iFp)
GO(gtk_text_iter_get_visible_slice, pFpp)
GO(gtk_text_iter_get_visible_text, pFpp)
GO(gtk_text_iter_has_tag, iFpp)
GO(gtk_text_iter_in_range, iFppp)
GO(gtk_text_iter_inside_sentence, iFp)
GO(gtk_text_iter_inside_word, iFp)
GO(gtk_text_iter_is_cursor_position, iFp)
GO(gtk_text_iter_is_end, iFp)
GO(gtk_text_iter_is_start, iFp)
GO(gtk_text_iter_order, vFpp)
GO(gtk_text_iter_set_line, vFpi)
GO(gtk_text_iter_set_line_index, vFpi)
GO(gtk_text_iter_set_line_offset, vFpi)
GO(gtk_text_iter_set_offset, vFpi)
GO(gtk_text_iter_set_visible_line_index, vFpi)
GO(gtk_text_iter_set_visible_line_offset, vFpi)
GO(gtk_text_iter_starts_line, iFp)
GO(gtk_text_iter_starts_sentence, iFp)
GO(gtk_text_iter_starts_word, iFp)
GO(gtk_text_iter_toggles_tag, iFpp)
//GO(gtk_text_layout_changed, 
//GO(gtk_text_layout_clamp_iter_to_vrange, 
//GO(gtk_text_layout_cursors_changed, 
//GO(gtk_text_layout_default_style_changed, 
//GO(gtk_text_layout_draw, 
//GO(gtk_text_layout_free_line_data, 
//GO(gtk_text_layout_free_line_display, 
//GO(gtk_text_layout_get_buffer, 
//GO(gtk_text_layout_get_cursor_locations, 
//GO(gtk_text_layout_get_cursor_visible, 
//GO(gtk_text_layout_get_iter_at_line, 
//GO(gtk_text_layout_get_iter_at_pixel, 
//GO(gtk_text_layout_get_iter_at_position, 
//GO(gtk_text_layout_get_iter_location, 
//GO(gtk_text_layout_get_line_at_y, 
//GO(gtk_text_layout_get_line_display, 
//GO(gtk_text_layout_get_lines, 
//GO(gtk_text_layout_get_line_yrange, 
//GO(gtk_text_layout_get_size, 
GO(gtk_text_layout_get_type, LFv) // Warning: failed to confirm
//GO(gtk_text_layout_invalidate, 
//GO(gtk_text_layout_invalidate_cursors, 
//GO(gtk_text_layout_is_valid, 
//GO(gtk_text_layout_iter_starts_line, 
//GO(gtk_text_layout_move_iter_to_line_end, 
//GO(gtk_text_layout_move_iter_to_next_line, 
//GO(gtk_text_layout_move_iter_to_previous_line, 
//GO(gtk_text_layout_move_iter_to_x, 
//GO(gtk_text_layout_move_iter_visually, 
//GO(gtk_text_layout_new, 
//GO(gtk_text_layout_set_buffer, 
//GO(gtk_text_layout_set_contexts, 
//GO(gtk_text_layout_set_cursor_direction, 
//GO(gtk_text_layout_set_cursor_visible, 
//GO(gtk_text_layout_set_default_style, 
//GO(gtk_text_layout_set_keyboard_direction, 
//GO(gtk_text_layout_set_overwrite_mode, 
//GO(gtk_text_layout_set_preedit_string, 
//GO(gtk_text_layout_set_screen_width, 
//GO(gtk_text_layout_spew, 
//GO(gtk_text_layout_validate, 
//GO(gtk_text_layout_validate_yrange, 
//GO(gtk_text_layout_wrap, 
//GO(gtk_text_layout_wrap_loop_end, 
//GO(gtk_text_layout_wrap_loop_start, 
//GO(gtk_text_line_segment_split, 
GO(gtk_text_mark_get_buffer, pFp)
GO(gtk_text_mark_get_deleted, iFp)
GO(gtk_text_mark_get_left_gravity, iFp)
GO(gtk_text_mark_get_name, pFp)
GO(gtk_text_mark_get_type, LFv)
GO(gtk_text_mark_get_visible, iFp)
GO(gtk_text_mark_new, pFpi)
GO(gtk_text_mark_set_visible, vFpi)
GO(gtk_text_new, pFpp) // Warning: failed to confirm
GO(gtk_text_search_flags_get_type, LFv)
GO(gtk_text_set_adjustments, vFppp) // Warning: failed to confirm
GO(gtk_text_set_editable, vFpi) // Warning: failed to confirm
GO(gtk_text_set_line_wrap, vFpi) // Warning: failed to confirm
GO(gtk_text_set_point, vFpu) // Warning: failed to confirm
GO(gtk_text_set_word_wrap, vFpi) // Warning: failed to confirm
GO(gtk_text_tag_event, iFpppp)
GO(gtk_text_tag_get_priority, iFp)
GO(gtk_text_tag_get_type, LFv)
GO(gtk_text_tag_new, pFp)
GO(gtk_text_tag_set_priority, vFpi)
GO(gtk_text_tag_table_add, iFpp)
//GOM(gtk_text_tag_table_foreach, vFEppp)
GO(gtk_text_tag_table_get_size, iFp)
GO(gtk_text_tag_table_get_type, LFv)
GO(gtk_text_tag_table_lookup, pFpp)
GO(gtk_text_tag_table_new, pFv)
GO(gtk_text_tag_table_remove, vFpp)
GO(gtk_text_thaw, vFp) // Warning: failed to confirm
GO(gtk_text_view_add_child_at_anchor, vFppp)
GO(gtk_text_view_add_child_in_window, vFppuii)
GO(gtk_text_view_backward_display_line, iFpp)
GO(gtk_text_view_backward_display_line_start, iFpp)
GO(gtk_text_view_buffer_to_window_coords, vFpuiipp)
GO(gtk_text_view_forward_display_line, iFpp)
GO(gtk_text_view_forward_display_line_end, iFpp)
GO(gtk_text_view_get_accepts_tab, iFp)
GO(gtk_text_view_get_border_window_size, iFpu)
GO(gtk_text_view_get_buffer, pFp)
GO(gtk_text_view_get_cursor_visible, iFp)
GO(gtk_text_view_get_default_attributes, pFp)
GO(gtk_text_view_get_editable, iFp)
GO(gtk_text_view_get_hadjustment, pFp)
GO(gtk_text_view_get_indent, iFp)
GO(gtk_text_view_get_iter_at_location, iFppii)
GO(gtk_text_view_get_iter_at_position, iFpppii)
GO(gtk_text_view_get_iter_location, vFppp)
GO(gtk_text_view_get_justification, uFp)
GO(gtk_text_view_get_left_margin, iFp)
GO(gtk_text_view_get_line_at_y, vFppip)
GO(gtk_text_view_get_line_yrange, vFpppp)
GO(gtk_text_view_get_overwrite, iFp)
GO(gtk_text_view_get_pixels_above_lines, iFp)
GO(gtk_text_view_get_pixels_below_lines, iFp)
GO(gtk_text_view_get_pixels_inside_wrap, iFp)
GO(gtk_text_view_get_right_margin, iFp)
GO(gtk_text_view_get_tabs, pFp)
GO(gtk_text_view_get_type, LFv)
GO(gtk_text_view_get_vadjustment, pFp)
GO(gtk_text_view_get_visible_rect, vFpp)
GO(gtk_text_view_get_window, pFpu)
GO(gtk_text_view_get_window_type, uFpp)
GO(gtk_text_view_get_wrap_mode, uFp)
GO(gtk_text_view_im_context_filter_keypress, iFpp)
GO(gtk_text_view_move_child, vFppii)
GO(gtk_text_view_move_mark_onscreen, iFpp)
GO(gtk_text_view_move_visually, iFppi)
GO(gtk_text_view_new, pFv)
GO(gtk_text_view_new_with_buffer, pFp)
GO(gtk_text_view_place_cursor_onscreen, iFp)
GO(gtk_text_view_reset_im_context, vFp)
GO(gtk_text_view_scroll_mark_onscreen, vFpp)
GO(gtk_text_view_scroll_to_iter, iFppdidd)
GO(gtk_text_view_scroll_to_mark, vFppdidd)
GO(gtk_text_view_set_accepts_tab, vFpi)
GO(gtk_text_view_set_border_window_size, vFpui)
GO(gtk_text_view_set_buffer, vFpp)
GO(gtk_text_view_set_cursor_visible, vFpi)
GO(gtk_text_view_set_editable, vFpi)
GO(gtk_text_view_set_indent, vFpi)
GO(gtk_text_view_set_justification, vFpu)
GO(gtk_text_view_set_left_margin, vFpi)
GO(gtk_text_view_set_overwrite, vFpi)
GO(gtk_text_view_set_pixels_above_lines, vFpi)
GO(gtk_text_view_set_pixels_below_lines, vFpi)
GO(gtk_text_view_set_pixels_inside_wrap, vFpi)
GO(gtk_text_view_set_right_margin, vFpi)
GO(gtk_text_view_set_tabs, vFpp)
GO(gtk_text_view_set_wrap_mode, vFpu)
GO(gtk_text_view_starts_display_line, iFpp)
GO(gtk_text_view_window_to_buffer_coords, vFpuiipp)
GO(gtk_text_window_type_get_type, LFv)
//GO(gtk_theme_engine_create_rc_style, 
//GO(gtk_theme_engine_get, 
GO(gtk_theme_engine_get_type, LFv) // Warning: failed to confirm
GOM(gtk_timeout_add, uFEupp) // Warning: failed to confirm
//GOM(gtk_timeout_add_full, uFuBppB)
GO(gtk_timeout_remove, vFu) // Warning: failed to confirm
GO(gtk_tips_query_get_type, LFv) // Warning: failed to confirm
//GO(gtk_tips_query_new, 
//GO(gtk_tips_query_set_caller, 
//GO(gtk_tips_query_set_labels, 
//GO(gtk_tips_query_start_query, 
//GO(gtk_tips_query_stop_query, 
GO(gtk_toggle_action_get_active, iFp)
GO(gtk_toggle_action_get_draw_as_radio, iFp)
GO(gtk_toggle_action_get_type, LFv)
GO(gtk_toggle_action_new, pFpppp)
GO(gtk_toggle_action_set_active, vFpi)
GO(gtk_toggle_action_set_draw_as_radio, vFpi)
GO(gtk_toggle_action_toggled, vFp)
GO(gtk_toggle_button_get_active, iFp)
GO(gtk_toggle_button_get_inconsistent, iFp)
GO(gtk_toggle_button_get_mode, iFp)
GO(gtk_toggle_button_get_type, LFv)
GO(gtk_toggle_button_new, pFv)
GO(gtk_toggle_button_new_with_label, pFp)
GO(gtk_toggle_button_new_with_mnemonic, pFp)
GO(gtk_toggle_button_set_active, vFpi)
GO(gtk_toggle_button_set_inconsistent, vFpi)
GO(gtk_toggle_button_set_mode, vFpi)
GO(gtk_toggle_button_toggled, vFp)
GO(gtk_toggle_tool_button_get_active, iFp)
GO(gtk_toggle_tool_button_get_type, LFv)
GO(gtk_toggle_tool_button_new, pFv)
GO(gtk_toggle_tool_button_new_from_stock, pFp)
GO(gtk_toggle_tool_button_set_active, vFpi)
GOM(gtk_toolbar_append_element, pFEpippppppp) // Warning: failed to confirm
GOM(gtk_toolbar_append_item, pFEppppppp) // Warning: failed to confirm
GO(gtk_toolbar_append_space, vFp) // Warning: failed to confirm
GO(gtk_toolbar_append_widget, vFpppp) // Warning: failed to confirm
GO(gtk_toolbar_child_type_get_type, LFv) // Warning: failed to confirm
GO(gtk_toolbar_get_drop_index, iFpii)
GO(gtk_toolbar_get_icon_size, uFp)
GO(gtk_toolbar_get_item_index, iFpp)
GO(gtk_toolbar_get_n_items, iFp)
GO(gtk_toolbar_get_nth_item, pFpi)
GO(gtk_toolbar_get_orientation, iFp) // Warning: failed to confirm
GO(gtk_toolbar_get_relief_style, uFp)
GO(gtk_toolbar_get_show_arrow, iFp)
GO(gtk_toolbar_get_style, uFp)
GO(gtk_toolbar_get_tooltips, iFp) // Warning: failed to confirm
GO(gtk_toolbar_get_type, LFv)
GO(gtk_toolbar_insert, vFppi)
GOM(gtk_toolbar_insert_element, pFEpipppppppi) // Warning: failed to confirm
GOM(gtk_toolbar_insert_item, pFEpppppppi) // Warning: failed to confirm
GO(gtk_toolbar_insert_space, vFpi) // Warning: failed to confirm
GOM(gtk_toolbar_insert_stock, pFEppppppi) // Warning: failed to confirm
GO(gtk_toolbar_insert_widget, vFppppi) // Warning: failed to confirm
GO(gtk_toolbar_new, pFv)
GOM(gtk_toolbar_prepend_element, pFEpippppppp) // Warning: failed to confirm
GOM(gtk_toolbar_prepend_item, pFEppppppp) // Warning: failed to confirm
GO(gtk_toolbar_prepend_space, vFp) // Warning: failed to confirm
GO(gtk_toolbar_prepend_widget, vFpppp) // Warning: failed to confirm
GO(gtk_toolbar_remove_space, vFpi) // Warning: failed to confirm
GO(gtk_toolbar_set_drop_highlight_item, vFppi)
GO(gtk_toolbar_set_icon_size, vFpu)
GO(gtk_toolbar_set_orientation, vFpi) // Warning: failed to confirm
GO(gtk_toolbar_set_show_arrow, vFpi)
GO(gtk_toolbar_set_style, vFpu)
GO(gtk_toolbar_set_tooltips, vFpi) // Warning: failed to confirm
GO(gtk_toolbar_space_style_get_type, LFv)
GO(gtk_toolbar_style_get_type, LFv)
GO(gtk_toolbar_unset_icon_size, vFp)
GO(gtk_toolbar_unset_style, vFp)
GO(gtk_tool_button_get_icon_name, pFp)
GO(gtk_tool_button_get_icon_widget, pFp)
GO(gtk_tool_button_get_label, pFp)
GO(gtk_tool_button_get_label_widget, pFp)
GO(gtk_tool_button_get_stock_id, pFp)
GO(gtk_tool_button_get_type, LFv)
GO(gtk_tool_button_get_use_underline, iFp)
GO(gtk_tool_button_new, pFpp)
GO(gtk_tool_button_new_from_stock, pFp)
GO(gtk_tool_button_set_icon_name, vFpp)
GO(gtk_tool_button_set_icon_widget, vFpp)
GO(gtk_tool_button_set_label, vFpp)
GO(gtk_tool_button_set_label_widget, vFpp)
GO(gtk_tool_button_set_stock_id, vFpp)
GO(gtk_tool_button_set_use_underline, vFpi)
GO(gtk_tool_item_get_ellipsize_mode, uFp)
GO(gtk_tool_item_get_expand, iFp)
GO(gtk_tool_item_get_homogeneous, iFp)
GO(gtk_tool_item_get_icon_size, uFp)
GO(gtk_tool_item_get_is_important, iFp)
GO(gtk_tool_item_get_orientation, uFp)
GO(gtk_tool_item_get_proxy_menu_item, pFpp)
GO(gtk_tool_item_get_relief_style, uFp)
GO(gtk_tool_item_get_text_alignment, fFp)
GO(gtk_tool_item_get_text_orientation, uFp)
GO(gtk_tool_item_get_text_size_group, pFp)
GO(gtk_tool_item_get_toolbar_style, uFp)
GO(gtk_tool_item_get_type, LFv)
GO(gtk_tool_item_get_use_drag_window, iFp)
GO(gtk_tool_item_get_visible_horizontal, iFp)
GO(gtk_tool_item_get_visible_vertical, iFp)
GO(gtk_tool_item_group_get_collapsed, iFp)
GO(gtk_tool_item_group_get_drop_item, pFpii)
GO(gtk_tool_item_group_get_ellipsize, uFp)
GO(gtk_tool_item_group_get_header_relief, uFp)
GO(gtk_tool_item_group_get_item_position, iFpp)
GO(gtk_tool_item_group_get_label, pFp)
GO(gtk_tool_item_group_get_label_widget, pFp)
GO(gtk_tool_item_group_get_n_items, uFp)
GO(gtk_tool_item_group_get_nth_item, pFpu)
GO(gtk_tool_item_group_get_type, LFv)
GO(gtk_tool_item_group_insert, vFppi)
GO(gtk_tool_item_group_new, pFp)
GO(gtk_tool_item_group_set_collapsed, vFpi)
GO(gtk_tool_item_group_set_ellipsize, vFpu)
GO(gtk_tool_item_group_set_header_relief, vFpu)
GO(gtk_tool_item_group_set_item_position, vFppi)
GO(gtk_tool_item_group_set_label, vFpp)
GO(gtk_tool_item_group_set_label_widget, vFpp)
GO(gtk_tool_item_new, pFv)
GO(gtk_tool_item_rebuild_menu, vFp)
GO(gtk_tool_item_retrieve_proxy_menu_item, pFp)
GO(gtk_tool_item_set_expand, vFpi)
GO(gtk_tool_item_set_homogeneous, vFpi)
GO(gtk_tool_item_set_is_important, vFpi)
GO(gtk_tool_item_set_proxy_menu_item, vFppp)
//GO(gtk_tool_item_set_tooltip, 
GO(gtk_tool_item_set_tooltip_markup, vFpp)
GO(gtk_tool_item_set_tooltip_text, vFpp)
GO(gtk_tool_item_set_use_drag_window, vFpi)
GO(gtk_tool_item_set_visible_horizontal, vFpi)
GO(gtk_tool_item_set_visible_vertical, vFpi)
GO(gtk_tool_item_toolbar_reconfigured, vFp)
GO(gtk_tool_palette_add_drag_dest, vFppuuu)
GO(gtk_tool_palette_drag_targets_get_type, LFv)
GO(gtk_tool_palette_get_drag_item, pFpp)
GO(gtk_tool_palette_get_drag_target_group, pFv)
GO(gtk_tool_palette_get_drag_target_item, pFv)
GO(gtk_tool_palette_get_drop_group, pFpii)
GO(gtk_tool_palette_get_drop_item, pFpii)
GO(gtk_tool_palette_get_exclusive, iFpp)
GO(gtk_tool_palette_get_expand, iFpp)
GO(gtk_tool_palette_get_group_position, iFpp)
GO(gtk_tool_palette_get_hadjustment, pFp)
GO(gtk_tool_palette_get_icon_size, uFp)
GO(gtk_tool_palette_get_style, uFp)
GO(gtk_tool_palette_get_type, LFv)
GO(gtk_tool_palette_get_vadjustment, pFp)
GO(gtk_tool_palette_new, pFv)
GO(gtk_tool_palette_set_drag_source, vFpu)
GO(gtk_tool_palette_set_exclusive, vFppi)
GO(gtk_tool_palette_set_expand, vFppi)
GO(gtk_tool_palette_set_group_position, vFppi)
GO(gtk_tool_palette_set_icon_size, vFpu)
GO(gtk_tool_palette_set_style, vFpu)
GO(gtk_tool_palette_unset_icon_size, vFp)
GO(gtk_tool_palette_unset_style, vFp)
GO(gtk_tool_shell_get_ellipsize_mode, uFp)
GO(gtk_tool_shell_get_icon_size, uFp)
GO(gtk_tool_shell_get_orientation, uFp)
GO(gtk_tool_shell_get_relief_style, uFp)
GO(gtk_tool_shell_get_style, uFp)
GO(gtk_tool_shell_get_text_alignment, fFp)
GO(gtk_tool_shell_get_text_orientation, uFp)
GO(gtk_tool_shell_get_text_size_group, pFp)
GO(gtk_tool_shell_get_type, LFv)
GO(gtk_tool_shell_rebuild_menu, vFp)
GO(gtk_tooltip_get_type, LFv)
GO(gtk_tooltips_data_get, pFp) // Warning: failed to confirm
GO(gtk_tooltips_disable, vFp) // Warning: failed to confirm
GO(gtk_tooltips_enable, vFp) // Warning: failed to confirm
GO(gtk_tooltip_set_custom, vFpp)
GO(gtk_tooltip_set_icon, vFpp)
GO(gtk_tooltip_set_icon_from_gicon, vFppu)
GO(gtk_tooltip_set_icon_from_icon_name, vFppu)
GO(gtk_tooltip_set_icon_from_stock, vFppu)
GO(gtk_tooltip_set_markup, vFpp)
GO(gtk_tooltip_set_text, vFpp)
GO(gtk_tooltip_set_tip_area, vFpp)
GO(gtk_tooltips_force_window, vFp) // Warning: failed to confirm
GO(gtk_tooltips_get_info_from_tip_window, iFppp) // Warning: failed to confirm
GO(gtk_tooltips_get_type, LFv) // Warning: failed to confirm
GO(gtk_tooltips_new, pFv) // Warning: failed to confirm
GO(gtk_tooltips_set_delay, vFpu) // Warning: failed to confirm
GO(gtk_tooltips_set_tip, vFpppp) // Warning: failed to confirm
GO(gtk_tooltip_trigger_tooltip_query, vFp)
GO(gtk_tray_icon_get_type, LFv) // Warning: failed to confirm
//GO(gtk_tree_append, 
//GO(gtk_tree_child_position, 
//GO(gtk_tree_clear_items, 
GO(gtk_tree_drag_dest_drag_data_received, iFppp)
GO(gtk_tree_drag_dest_get_type, LFv)
GO(gtk_tree_drag_dest_row_drop_possible, iFppp)
GO(gtk_tree_drag_source_drag_data_delete, iFpp)
GO(gtk_tree_drag_source_drag_data_get, iFppp)
GO(gtk_tree_drag_source_get_type, LFv)
GO(gtk_tree_drag_source_row_draggable, iFpp)
GO(gtk_tree_get_row_drag_data, iFppp)
GO(gtk_tree_get_type, LFv) // Warning: failed to confirm
//GO(gtk_tree_insert, 
//GO(gtk_tree_item_collapse, 
//GO(gtk_tree_item_deselect, 
//GO(gtk_tree_item_expand, 
GO(gtk_tree_item_get_type, LFv) // Warning: failed to confirm
//GO(gtk_tree_item_new, 
//GO(gtk_tree_item_new_with_label, 
//GO(gtk_tree_item_remove_subtree, 
//GO(gtk_tree_item_select, 
//GO(gtk_tree_item_set_subtree, 
GO(gtk_tree_iter_copy, pFp)
GO(gtk_tree_iter_free, vFp)
GO(gtk_tree_iter_get_type, LFv)
GO(gtk_tree_model_filter_clear_cache, vFp)
GO(gtk_tree_model_filter_convert_child_iter_to_iter, iFppp)
GO(gtk_tree_model_filter_convert_child_path_to_path, pFpp)
GO(gtk_tree_model_filter_convert_iter_to_child_iter, vFppp)
GO(gtk_tree_model_filter_convert_path_to_child_path, pFpp)
GO(gtk_tree_model_filter_get_model, pFp)
GO(gtk_tree_model_filter_get_type, LFv)
GO(gtk_tree_model_filter_new, pFpp)
GO(gtk_tree_model_filter_refilter, vFp)
//GOM(gtk_tree_model_filter_set_modify_func, vFpipppp)
GO(gtk_tree_model_filter_set_visible_column, vFpi)
//GOM(gtk_tree_model_filter_set_visible_func, vFpppp)
GO(gtk_tree_model_flags_get_type, LFv)
//GOM(gtk_tree_model_foreach, vFEppp)
//GOM(gtk_tree_model_get, vFppV)
GO(gtk_tree_model_get_column_type, LFpi)
GO(gtk_tree_model_get_flags, uFp)
GO(gtk_tree_model_get_iter, iFppp)
GO(gtk_tree_model_get_iter_first, iFpp)
GO(gtk_tree_model_get_iter_from_string, iFppp)
GO(gtk_tree_model_get_n_columns, iFp)
GO(gtk_tree_model_get_path, pFpp)
GO(gtk_tree_model_get_string_from_iter, pFpp)
GO(gtk_tree_model_get_type, LFv)
//GOM(gtk_tree_model_get_valist, vFppA)
GO(gtk_tree_model_get_value, vFppip)
GO(gtk_tree_model_iter_children, iFppp)
GO(gtk_tree_model_iter_has_child, iFpp)
GO(gtk_tree_model_iter_n_children, iFpp)
GO(gtk_tree_model_iter_next, iFpp)
GO(gtk_tree_model_iter_nth_child, iFpppi)
GO(gtk_tree_model_iter_parent, iFppp)
GO(gtk_tree_model_ref_node, vFpp)
GO(gtk_tree_model_row_changed, vFppp)
GO(gtk_tree_model_row_deleted, vFpp)
GO(gtk_tree_model_row_has_child_toggled, vFppp)
GO(gtk_tree_model_row_inserted, vFppp)
GO(gtk_tree_model_rows_reordered, vFpppp)
GO(gtk_tree_model_sort_clear_cache, vFp)
GO(gtk_tree_model_sort_convert_child_iter_to_iter, iFppp)
GO(gtk_tree_model_sort_convert_child_path_to_path, pFpp)
GO(gtk_tree_model_sort_convert_iter_to_child_iter, vFppp)
GO(gtk_tree_model_sort_convert_path_to_child_path, pFpp)
GO(gtk_tree_model_sort_get_model, pFp)
GO(gtk_tree_model_sort_get_type, LFv)
GO(gtk_tree_model_sort_iter_is_valid, iFpp)
GO(gtk_tree_model_sort_new_with_model, pFp)
GO(gtk_tree_model_sort_reset_default_sort_func, vFp)
GO(gtk_tree_model_unref_node, vFpp)
//GO(gtk_tree_new, 
GO(gtk_tree_path_append_index, vFpi)
GO(gtk_tree_path_compare, iFpp)
GO(gtk_tree_path_copy, pFp)
GO(gtk_tree_path_down, vFp)
GO(gtk_tree_path_free, vFp)
GO(gtk_tree_path_get_depth, iFp)
GO(gtk_tree_path_get_indices, pFp)
GO(gtk_tree_path_get_indices_with_depth, pFpp)
GO(gtk_tree_path_get_type, LFv)
GO(gtk_tree_path_is_ancestor, iFpp)
GO(gtk_tree_path_is_descendant, iFpp)
GO(gtk_tree_path_new, pFv)
GO(gtk_tree_path_new_first, pFv)
GO(gtk_tree_path_new_from_indices, pFippppppppppppppppp)  // vaarg
GO(gtk_tree_path_new_from_string, pFp)
GO(gtk_tree_path_next, vFp)
GO(gtk_tree_path_prepend_index, vFpi)
GO(gtk_tree_path_prev, iFp)
GO(gtk_tree_path_to_string, pFp)
GO(gtk_tree_path_up, iFp)
//GO(gtk_tree_prepend, 
//GO(gtk_tree_remove_item, 
//GO(gtk_tree_remove_items, 
GO(gtk_tree_row_reference_copy, pFp)
GO(gtk_tree_row_reference_deleted, vFpp)
GO(gtk_tree_row_reference_free, vFp)
GO(gtk_tree_row_reference_get_model, pFp)
GO(gtk_tree_row_reference_get_path, pFp)
GO(gtk_tree_row_reference_get_type, LFv)
GO(gtk_tree_row_reference_inserted, vFpp)
GO(gtk_tree_row_reference_new, pFpp)
GO(gtk_tree_row_reference_new_proxy, pFppp)
GO(gtk_tree_row_reference_reordered, vFpppp)
GO(gtk_tree_row_reference_valid, iFp)
//GO(gtk_tree_select_child, 
GO(gtk_tree_selection_count_selected_rows, iFp)
GO(gtk_tree_selection_get_mode, uFp)
GO(gtk_tree_selection_get_selected, iFppp)
GO(gtk_tree_selection_get_selected_rows, pFpp)
//GOM(gtk_tree_selection_get_select_function, pFEp)
GO(gtk_tree_selection_get_tree_view, pFp)
GO(gtk_tree_selection_get_type, LFv)
//GOM(gtk_tree_selection_get_user_data, pFEp)
GO(gtk_tree_selection_iter_is_selected, iFpp)
GO(gtk_tree_selection_path_is_selected, iFpp)
GO(gtk_tree_selection_select_all, vFp)
//GOM(gtk_tree_selection_selected_foreach, vFEppp)
GO(gtk_tree_selection_select_iter, vFpp)
GO(gtk_tree_selection_select_path, vFpp)
GO(gtk_tree_selection_select_range, vFppp)
GO(gtk_tree_selection_set_mode, vFpu)
//GOM(gtk_tree_selection_set_select_function, vFEpppp)
GO(gtk_tree_selection_unselect_all, vFp)
GO(gtk_tree_selection_unselect_iter, vFpp)
GO(gtk_tree_selection_unselect_path, vFpp)
GO(gtk_tree_selection_unselect_range, vFppp)
//GO(gtk_tree_select_item, 
GO(gtk_tree_set_row_drag_data, iFppp)
//GO(gtk_tree_set_selection_mode, 
//GO(gtk_tree_set_view_lines, 
//GO(gtk_tree_set_view_mode, 
GO(gtk_tree_sortable_get_sort_column_id, iFppp)
GO(gtk_tree_sortable_get_type, LFv)
GO(gtk_tree_sortable_has_default_sort_func, iFp)
GOM(gtk_tree_sortable_set_default_sort_func, vFEpppp)
GO(gtk_tree_sortable_set_sort_column_id, vFpiu)
GOM(gtk_tree_sortable_set_sort_func, vFEpippp)
GO(gtk_tree_sortable_sort_column_changed, vFp)
GO(gtk_tree_store_append, vFppp)
GO(gtk_tree_store_clear, vFp)
GO(gtk_tree_store_get_type, LFv)
GO(gtk_tree_store_insert, vFpppi)
GO(gtk_tree_store_insert_after, vFpppp)
GO(gtk_tree_store_insert_before, vFpppp)
//GOM(gtk_tree_store_insert_with_values, vFpppiV)
GO(gtk_tree_store_insert_with_valuesv, vFpppippi)
GO(gtk_tree_store_is_ancestor, iFppp)
GO(gtk_tree_store_iter_depth, iFpp)
GO(gtk_tree_store_iter_is_valid, iFpp)
GO(gtk_tree_store_move_after, vFppp)
GO(gtk_tree_store_move_before, vFppp)
GOM(gtk_tree_store_new, pFEiV)
GO(gtk_tree_store_newv, pFip)
GO(gtk_tree_store_prepend, vFppp)
GO(gtk_tree_store_remove, iFpp)
GO(gtk_tree_store_reorder, vFppp)
GOM(gtk_tree_store_set, vFEppV)
GO(gtk_tree_store_set_column_types, vFpip)
GOM(gtk_tree_store_set_valist, vFEppA)
GO(gtk_tree_store_set_value, vFppip)
GO(gtk_tree_store_set_valuesv, vFppppi)
GO(gtk_tree_store_swap, vFppp)
//GO(gtk_tree_unselect_child, 
//GO(gtk_tree_unselect_item, 
GO(gtk_tree_view_append_column, iFpp)
GO(gtk_tree_view_collapse_all, vFp)
GO(gtk_tree_view_collapse_row, iFpp)
GO(gtk_tree_view_column_add_attribute, vFpppi)
GO(gtk_tree_view_column_cell_get_position, iFpppp)
GO(gtk_tree_view_column_cell_get_size, vFpppppp)
GO(gtk_tree_view_column_cell_is_visible, iFp)
GO(gtk_tree_view_column_cell_set_cell_data, vFpppii)
GO(gtk_tree_view_column_clear, vFp)
GO(gtk_tree_view_column_clear_attributes, vFpp)
GO(gtk_tree_view_column_clicked, vFp)
GO(gtk_tree_view_column_focus_cell, vFpp)
GO(gtk_tree_view_column_get_alignment, fFp)
GO(gtk_tree_view_column_get_button, pFp)
GO(gtk_tree_view_column_get_cell_renderers, pFp) // Warning: failed to confirm
GO(gtk_tree_view_column_get_clickable, iFp)
GO(gtk_tree_view_column_get_expand, iFp)
GO(gtk_tree_view_column_get_fixed_width, iFp)
GO(gtk_tree_view_column_get_max_width, iFp)
GO(gtk_tree_view_column_get_min_width, iFp)
GO(gtk_tree_view_column_get_reorderable, iFp)
GO(gtk_tree_view_column_get_resizable, iFp)
GO(gtk_tree_view_column_get_sizing, uFp)
GO(gtk_tree_view_column_get_sort_column_id, iFp)
GO(gtk_tree_view_column_get_sort_indicator, iFp)
GO(gtk_tree_view_column_get_sort_order, uFp)
GO(gtk_tree_view_column_get_spacing, iFp)
GO(gtk_tree_view_column_get_title, pFp)
GO(gtk_tree_view_column_get_tree_view, pFp)
GO(gtk_tree_view_column_get_type, LFv)
GO(gtk_tree_view_column_get_visible, iFp)
GO(gtk_tree_view_column_get_widget, pFp)
GO(gtk_tree_view_column_get_width, iFp)
GO(gtk_tree_view_column_new, pFv)
GO(gtk_tree_view_column_new_with_attributes, pFppppppppppppp)   //vaarg
GO(gtk_tree_view_column_pack_end, vFppi)
GO(gtk_tree_view_column_pack_start, vFppi)
GO(gtk_tree_view_column_queue_resize, vFp)
GO(gtk_tree_view_columns_autosize, vFp)
GO(gtk_tree_view_column_set_alignment, vFpf)
//GOM(gtk_tree_view_column_set_attributes, vFppV)
GOM(gtk_tree_view_column_set_cell_data_func, vFEppppp)
GO(gtk_tree_view_column_set_clickable, vFpi)
GO(gtk_tree_view_column_set_expand, vFpi)
GO(gtk_tree_view_column_set_fixed_width, vFpi)
GO(gtk_tree_view_column_set_max_width, vFpi)
GO(gtk_tree_view_column_set_min_width, vFpi)
GO(gtk_tree_view_column_set_reorderable, vFpi)
GO(gtk_tree_view_column_set_resizable, vFpi)
GO(gtk_tree_view_column_set_sizing, vFpu)
GO(gtk_tree_view_column_set_sort_column_id, vFpi)
GO(gtk_tree_view_column_set_sort_indicator, vFpi)
GO(gtk_tree_view_column_set_sort_order, vFpu)
GO(gtk_tree_view_column_set_spacing, vFpi)
GO(gtk_tree_view_column_set_title, vFpp)
GO(gtk_tree_view_column_set_visible, vFpi)
GO(gtk_tree_view_column_set_widget, vFpp)
GO(gtk_tree_view_column_sizing_get_type, LFv)
GO(gtk_tree_view_convert_bin_window_to_tree_coords, vFpiipp)
GO(gtk_tree_view_convert_bin_window_to_widget_coords, vFpiipp)
GO(gtk_tree_view_convert_tree_to_bin_window_coords, vFpiipp)
GO(gtk_tree_view_convert_tree_to_widget_coords, vFpiipp)
GO(gtk_tree_view_convert_widget_to_bin_window_coords, vFpiipp)
GO(gtk_tree_view_convert_widget_to_tree_coords, vFpiipp)
GO(gtk_tree_view_create_row_drag_icon, pFpp)
GO(gtk_tree_view_drop_position_get_type, LFv)
GO(gtk_tree_view_enable_model_drag_dest, vFppiu)
GO(gtk_tree_view_enable_model_drag_source, vFpupiu)
GO(gtk_tree_view_expand_all, vFp)
GO(gtk_tree_view_expand_row, iFppi)
GO(gtk_tree_view_expand_to_path, vFpp)
GO(gtk_tree_view_get_background_area, vFpppp)
GO(gtk_tree_view_get_bin_window, pFp)
GO(gtk_tree_view_get_cell_area, vFpppp)
GO(gtk_tree_view_get_column, pFpi)
GO(gtk_tree_view_get_columns, pFp)
GO(gtk_tree_view_get_cursor, vFppp)
GO(gtk_tree_view_get_dest_row_at_pos, iFpiipp)
GO(gtk_tree_view_get_drag_dest_row, vFppp)
GO(gtk_tree_view_get_enable_search, iFp)
GO(gtk_tree_view_get_enable_tree_lines, iFp)
GO(gtk_tree_view_get_expander_column, pFp)
GO(gtk_tree_view_get_fixed_height_mode, iFp)
GO(gtk_tree_view_get_grid_lines, uFp)
GO(gtk_tree_view_get_hadjustment, pFp)
GO(gtk_tree_view_get_headers_clickable, iFp)
GO(gtk_tree_view_get_headers_visible, iFp)
GO(gtk_tree_view_get_hover_expand, iFp)
GO(gtk_tree_view_get_hover_selection, iFp)
GO(gtk_tree_view_get_level_indentation, iFp)
GO(gtk_tree_view_get_model, pFp)
GO(gtk_tree_view_get_path_at_pos, iFpiipppp)
GO(gtk_tree_view_get_reorderable, iFp)
//GOM(gtk_tree_view_get_row_separator_func, pFEp)
GO(gtk_tree_view_get_rubber_banding, iFp)
GO(gtk_tree_view_get_rules_hint, iFp)
GO(gtk_tree_view_get_search_column, iFp)
GO(gtk_tree_view_get_search_entry, pFp)
//GOM(gtk_tree_view_get_search_equal_func, pFEp)
//GOM(gtk_tree_view_get_search_position_func, pFEp)
GO(gtk_tree_view_get_selection, pFp)
GO(gtk_tree_view_get_show_expanders, iFp)
GO(gtk_tree_view_get_tooltip_column, iFp)
GO(gtk_tree_view_get_tooltip_context, iFpppippp)
GO(gtk_tree_view_get_type, LFv)
GO(gtk_tree_view_get_vadjustment, pFp)
GO(gtk_tree_view_get_visible_range, iFppp)
GO(gtk_tree_view_get_visible_rect, vFpp)
GO(gtk_tree_view_grid_lines_get_type, LFv)
GO(gtk_tree_view_insert_column, iFppi)
GO(gtk_tree_view_insert_column_with_attributes, iFpipppppppppppp) //vaarg
//GOM(gtk_tree_view_insert_column_with_data_func, iFpippBpB)
GO(gtk_tree_view_is_rubber_banding_active, iFp)
//GOM(gtk_tree_view_map_expanded_rows, vFEppp)
GO(gtk_tree_view_mode_get_type, LFv) // Warning: failed to confirm
GO(gtk_tree_view_move_column_after, vFppp)
GO(gtk_tree_view_new, pFv)
GO(gtk_tree_view_new_with_model, pFp)
GO(gtk_tree_view_remove_column, iFpp)
GO(gtk_tree_view_row_activated, vFppp)
GO(gtk_tree_view_row_expanded, iFpp)
GO(gtk_tree_view_scroll_to_cell, vFpppiff)
GO(gtk_tree_view_scroll_to_point, vFpii)
//GOM(gtk_tree_view_set_column_drag_function, vFEpppp)
GO(gtk_tree_view_set_cursor, vFpppi)
GO(gtk_tree_view_set_cursor_on_cell, vFppppi)
//GOM(gtk_tree_view_set_destroy_count_func, vFEpppp)
GO(gtk_tree_view_set_drag_dest_row, vFppu)
GO(gtk_tree_view_set_enable_search, vFpi)
GO(gtk_tree_view_set_enable_tree_lines, vFpi)
GO(gtk_tree_view_set_expander_column, vFpp)
GO(gtk_tree_view_set_fixed_height_mode, vFpi)
GO(gtk_tree_view_set_grid_lines, vFpu)
GO(gtk_tree_view_set_hadjustment, vFpp)
GO(gtk_tree_view_set_headers_clickable, vFpi)
GO(gtk_tree_view_set_headers_visible, vFpi)
GO(gtk_tree_view_set_hover_expand, vFpi)
GO(gtk_tree_view_set_hover_selection, vFpi)
GO(gtk_tree_view_set_level_indentation, vFpi)
GO(gtk_tree_view_set_model, vFpp)
GO(gtk_tree_view_set_reorderable, vFpi)
//GOM(gtk_tree_view_set_row_separator_func, vFEpppp)
GO(gtk_tree_view_set_rubber_banding, vFpi)
GO(gtk_tree_view_set_rules_hint, vFpi)
GO(gtk_tree_view_set_search_column, vFpi)
GO(gtk_tree_view_set_search_entry, vFpp)
GOM(gtk_tree_view_set_search_equal_func, vFEpppp)
//GOM(gtk_tree_view_set_search_position_func, vFEpppp)
GO(gtk_tree_view_set_show_expanders, vFpi)
GO(gtk_tree_view_set_tooltip_cell, vFppppp)
GO(gtk_tree_view_set_tooltip_column, vFpi)
GO(gtk_tree_view_set_tooltip_row, vFppp)
GO(gtk_tree_view_set_vadjustment, vFpp)
GO(gtk_tree_view_tree_to_widget_coords, vFpiipp) // Warning: failed to confirm
GO(gtk_tree_view_unset_rows_drag_dest, vFp)
GO(gtk_tree_view_unset_rows_drag_source, vFp)
GO(gtk_tree_view_widget_to_tree_coords, vFpiipp) // Warning: failed to confirm
GO(gtk_true, iFv)
GOM(gtk_type_class, pFEi) // Warning: failed to confirm
GO(gtk_type_enum_find_value, pFip) // Warning: failed to confirm
GO(gtk_type_enum_get_values, pFi) // Warning: failed to confirm
GO(gtk_type_flags_find_value, pFip) // Warning: failed to confirm
GO(gtk_type_flags_get_values, pFi) // Warning: failed to confirm
GO(gtk_type_init, vFi) // Warning: failed to confirm
GO(gtk_type_new, pFi) // Warning: failed to confirm
GOM(gtk_type_unique, iFELp) // Warning: failed to confirm
GO(gtk_ui_manager_add_ui, vFpupppui)
GO(gtk_ui_manager_add_ui_from_file, uFppp)
GO(gtk_ui_manager_add_ui_from_string, uFpplp)
GO(gtk_ui_manager_ensure_update, vFp)
GO(gtk_ui_manager_get_accel_group, pFp)
GO(gtk_ui_manager_get_action, pFpp)
GO(gtk_ui_manager_get_action_groups, pFp)
GO(gtk_ui_manager_get_add_tearoffs, iFp)
GO(gtk_ui_manager_get_toplevels, pFpu)
GO(gtk_ui_manager_get_type, LFv)
GO(gtk_ui_manager_get_ui, pFp)
GO(gtk_ui_manager_get_widget, pFpp)
GO(gtk_ui_manager_insert_action_group, vFppi)
GO(gtk_ui_manager_item_type_get_type, LFv)
GO(gtk_ui_manager_new, pFv)
GO(gtk_ui_manager_new_merge_id, uFp)
GO(gtk_ui_manager_remove_action_group, vFpp)
GO(gtk_ui_manager_remove_ui, vFpu)
GO(gtk_ui_manager_set_add_tearoffs, vFpi)
GO(gtk_unit_get_type, LFv)
GO(gtk_update_type_get_type, LFv) // Warning: failed to confirm
GO(gtk_vbox_get_type, LFv)
GO(gtk_vbox_new, pFii)
//GO(gtk_vbutton_box_get_layout_default, 
//GO(gtk_vbutton_box_get_spacing_default, 
GO(gtk_vbutton_box_get_type, LFv)
GO(gtk_vbutton_box_new, pFv)
//GO(gtk_vbutton_box_set_layout_default, 
//GO(gtk_vbutton_box_set_spacing_default, 
GO(gtk_viewport_get_bin_window, pFp)
GO(gtk_viewport_get_hadjustment, pFp)
GO(gtk_viewport_get_shadow_type, uFp)
GO(gtk_viewport_get_type, LFv)
GO(gtk_viewport_get_vadjustment, pFp)
GO(gtk_viewport_get_view_window, pFp)
GO(gtk_viewport_new, pFpp)
GO(gtk_viewport_set_hadjustment, vFpp)
GO(gtk_viewport_set_shadow_type, vFpu)
GO(gtk_viewport_set_vadjustment, vFpp)
GO(gtk_visibility_get_type, LFv) // Warning: failed to confirm
GO(gtk_volume_button_get_type, LFv)
GO(gtk_volume_button_new, pFv)
GO(gtk_vpaned_get_type, LFv)
GO(gtk_vpaned_new, pFv)
GO(gtk_vruler_get_type, LFv) // Warning: failed to confirm
GO(gtk_vruler_new, pFv) // Warning: failed to confirm
GO(gtk_vscale_get_type, LFv)
GO(gtk_vscale_new, pFp)
GO(gtk_vscale_new_with_range, pFddd)
GO(gtk_vscrollbar_get_type, LFv)
GO(gtk_vscrollbar_new, pFp)
GO(gtk_vseparator_get_type, LFv)
GO(gtk_vseparator_new, pFv)
GO(gtk_widget_activate, iFp)
GO(gtk_widget_add_accelerator, vFpppuuu)
GO(gtk_widget_add_events, vFpi)
GO(gtk_widget_add_mnemonic_label, vFpp)
GO(gtk_widget_can_activate_accel, iFpu)
GO(gtk_widget_child_focus, iFpu)
GO(gtk_widget_child_notify, vFpp)
GO(gtk_widget_class_bind_template_child_full, vFppil)
//GOM(gtk_widget_class_bind_template_callback_full, vFEppp)
GO(gtk_widget_class_find_style_property, pFpp)
GO(gtk_widget_class_install_style_property, vFpp)
//GOM(gtk_widget_class_install_style_property_parser, vFEppp)
GO(gtk_widget_class_list_style_properties, pFpp)
GO(gtk_widget_class_path, vFpppp)
GO(gtk_widget_class_set_accessible_role, vFpu)
GO(gtk_widget_class_set_accessible_type, vFpL)
//GOM(gtk_widget_class_set_connect_func, vFEpppp)
GO(gtk_widget_compute_expand, iFpu)
GO(gtk_widget_create_pango_context, pFp)
GO(gtk_widget_create_pango_layout, pFpp)
GO(gtk_widget_destroy, vFp)
GO(gtk_widget_destroyed, vFpp)
GO(gtk_widget_device_is_shadowed, iFpp)
GO(gtk_widget_draw, vFpp)
GO(gtk_widget_ensure_style, vFp)
GO(gtk_widget_error_bell, vFp)
GO(gtk_widget_event, iFpp)
GO(gtk_widget_flags_get_type, LFv) // Warning: failed to confirm
GO(gtk_widget_freeze_child_notify, vFp)
GO(gtk_widget_get_accessible, pFp)
GO(gtk_widget_get_action, pFp) // Warning: failed to confirm
GO(gtk_widget_get_allocation, vFpp)
GO(gtk_widget_get_allocated_width, iFp)
GO(gtk_widget_get_allocated_height, iFp)
GO(gtk_widget_get_ancestor, pFpL)
GO(gtk_widget_get_app_paintable, iFp)
GO(gtk_widget_get_can_default, iFp)
GO(gtk_widget_get_can_focus, iFp)
GO(gtk_widget_get_child_requisition, vFpp)
GO(gtk_widget_get_child_visible, iFp)
GO(gtk_widget_get_clip, vFpp)
GO(gtk_widget_get_clipboard, pFpp)
GO(gtk_widget_get_colormap, pFp) // Warning: failed to confirm
GO(gtk_widget_get_composite_name, pFp)
GO(gtk_widget_get_default_colormap, pFv) // Warning: failed to confirm
GO(gtk_widget_get_default_direction, uFv)
GO(gtk_widget_get_default_style, pFv)
GO(gtk_widget_get_default_visual, pFv) // Warning: failed to confirm
GO(gtk_widget_get_direction, uFp)
GO(gtk_widget_get_display, pFp)
GO(gtk_widget_get_double_buffered, iFp)
GO(gtk_widget_get_events, iFp)
GO(gtk_widget_get_extension_events, iFp) // Warning: failed to confirm
GO(gtk_widget_get_frame_clock, pFp)
GO(gtk_widget_get_halign, uFp)
GO(gtk_widget_get_has_tooltip, iFp)
GO(gtk_widget_get_has_window, iFp)
GO(gtk_widget_get_hexpand, iFp)
GO(gtk_widget_get_hexpand_set, iFp)
GO(gtk_widget_get_margin_bottom, iFp)
GO(gtk_widget_get_margin_end, iFp)
GO(gtk_widget_get_margin_left, iFp)
GO(gtk_widget_get_margin_right, iFp)
GO(gtk_widget_get_margin_start, iFp)
GO(gtk_widget_get_margin_top, iFp)
GO(gtk_widget_get_mapped, iFp)
GO(gtk_widget_get_modifier_style, pFp)
GO(gtk_widget_get_name, pFp)
GO(gtk_widget_get_native, pFp) // Warning: failed to confirm
GO(gtk_widget_get_no_show_all, iFp)
GO(gtk_widget_get_pango_context, pFp)
GO(gtk_widget_get_parent, pFp)
GO(gtk_widget_get_parent_window, pFp)
GO(gtk_widget_get_pointer, vFppp)
GO(gtk_widget_get_preferred_height, vFppp)
GO(gtk_widget_get_preferred_height_and_baseline_for_width, vFpipppp)
GO(gtk_widget_get_preferred_height_for_width, vFpipp)
GO(gtk_widget_get_preferred_size, vFppp)
GO(gtk_widget_get_preferred_width, vFppp)
GO(gtk_widget_get_preferred_width_for_height, vFpipp)
GO(gtk_widget_get_realized, iFp)
GO(gtk_widget_get_receives_default, iFp)
GO(gtk_widget_get_request_mode, uFp)
GO(gtk_widget_get_requisition, vFpp)
GO(gtk_widget_get_root_window, pFp)
GO(gtk_widget_get_scale_factor, iFp)
GO(gtk_widget_get_screen, pFp)
GO(gtk_widget_get_sensitive, iFp)
GO(gtk_widget_get_settings, pFp)
GO(gtk_widget_get_size_request, vFppp)
GO(gtk_widget_get_snapshot, pFpp) // Warning: failed to confirm
GO(gtk_widget_get_state, uFp)
GO(gtk_widget_get_state_flags, uFp)
GO(gtk_widget_get_style, pFp)
GO(gtk_widget_get_style_context, pFp)
GO(gtk_widget_get_template_child, pFpLp)
GO(gtk_widget_get_tooltip_markup, pFp)
GO(gtk_widget_get_tooltip_text, pFp)
GO(gtk_widget_get_tooltip_window, pFp)
GO(gtk_widget_get_toplevel, pFp)
GO(gtk_widget_get_type, LFv)
GO(gtk_widget_get_valign, uFp)
GO(gtk_widget_get_valign_with_baseline, uFp)
GO(gtk_widget_get_vexpand, iFp)
GO(gtk_widget_get_vexpand_set, iFp)
GO(gtk_widget_get_visible, iFp)
GO(gtk_widget_get_visual, pFp)
GO(gtk_widget_get_window, pFp)
GO(gtk_widget_grab_default, vFp)
GO(gtk_widget_grab_focus, vFp)
GO(gtk_widget_has_default, iFp)
GO(gtk_widget_has_focus, iFp)
GO(gtk_widget_has_grab, iFp)
GO(gtk_widget_has_rc_style, iFp)
GO(gtk_widget_has_screen, iFp)
GO(gtk_widget_help_type_get_type, LFv)
GO(gtk_widget_hide, vFp)
GO(gtk_widget_hide_all, vFp) // Warning: failed to confirm
GO(gtk_widget_hide_on_delete, iFp)
GO(gtk_widget_init_template, vFp)
GO(gtk_widget_input_shape_combine_mask, vFppii) // Warning: failed to confirm
GO(gtk_widget_intersect, iFppp)
GO(gtk_widget_is_ancestor, iFpp)
GO(gtk_widget_is_composited, iFp)
GO(gtk_widget_is_drawable, iFp)
GO(gtk_widget_is_focus, iFp)
GO(gtk_widget_is_sensitive, iFp)
GO(gtk_widget_is_toplevel, iFp)
GO(gtk_widget_keynav_failed, iFpu)
GO(gtk_widget_list_accel_closures, pFp)
GO(gtk_widget_list_mnemonic_labels, pFp)
GO(gtk_widget_map, vFp)
GO(gtk_widget_measure, vFpiipppp) // Warning: failed to confirm
GO(gtk_widget_mnemonic_activate, iFpi)
GO(gtk_widget_modify_base, vFpup)
GO(gtk_widget_modify_bg, vFpup)
GO(gtk_widget_modify_cursor, vFppp)
GO(gtk_widget_modify_fg, vFpup)
GO(gtk_widget_modify_font, vFpp)
GO(gtk_widget_modify_style, vFpp)
GO(gtk_widget_modify_text, vFpup)
GO(gtk_widget_new, pFppppppppppppp) //vaarg
GO(gtk_widget_path, vFpppp)
GO(gtk_widget_path_append_type, iFpL)
GO(gtk_widget_path_append_with_siblings, iFppu)
GO(gtk_widget_path_append_for_widget, iFpp)
GO(gtk_widget_path_copy, pFp)
GO(gtk_widget_path_free, vFp)
GO(gtk_widget_path_get_object_type, LFp)
GO(gtk_widget_path_has_parent, iFpL)
GO(gtk_widget_path_is_type, iFpL)
GO(gtk_widget_path_iter_add_class, vFpip)
GO(gtk_widget_path_iter_add_region, vFpipu)
GO(gtk_widget_path_iter_clear_classes, vFpi)
GO(gtk_widget_path_iter_clear_regions, vFpi)
GO(gtk_widget_path_iter_get_name, pFpi)
GO(gtk_widget_path_iter_get_object_name, pFpi)
GO(gtk_widget_path_iter_get_object_type, LFpi)
GO(gtk_widget_path_iter_get_siblings, pFpi)
GO(gtk_widget_path_iter_get_sibling_index, uFpi)
GO(gtk_widget_path_iter_get_state, uFpi)
GO(gtk_widget_path_iter_has_class, iFpip)
GO(gtk_widget_path_iter_has_name, iFpip)
GO(gtk_widget_path_iter_has_qclass, iFpiu)
GO(gtk_widget_path_iter_has_qname, iFpiu)
GO(gtk_widget_path_iter_has_qregion, iFpiup)
GO(gtk_widget_path_iter_has_region, iFpipp)
GO(gtk_widget_path_iter_list_classes, pFpi)
GO(gtk_widget_path_iter_list_regions, pFpi)
GO(gtk_widget_path_iter_remove_class, vFpip)
GO(gtk_widget_path_iter_remove_region, vFpip)
GO(gtk_widget_path_iter_set_name, vFpip)
GO(gtk_widget_path_iter_set_object_name, vFpip)
GO(gtk_widget_path_iter_set_object_type, vFpiL)
GO(gtk_widget_path_iter_set_state, vFpiu)
GO(gtk_widget_path_length, iFp)
GO(gtk_widget_path_new, pFv)
GO(gtk_widget_path_prepend_type, vFpL)
GO(gtk_widget_path_to_string, pFp)
GO(gtk_widget_path_ref, pFp)
GO(gtk_widget_path_unref, vFp)
GO(gtk_widget_pop_colormap, vFv) // Warning: failed to confirm
GO(gtk_widget_pop_composite_child, vFv)
GO(gtk_widget_push_colormap, vFp) // Warning: failed to confirm
GO(gtk_widget_push_composite_child, vFv)
GO(gtk_widget_queue_clear, vFp) // Warning: failed to confirm
GO(gtk_widget_queue_clear_area, vFpiiii) // Warning: failed to confirm
GO(gtk_widget_queue_draw, vFp)
GO(gtk_widget_queue_draw_area, vFpiiii)
GO(gtk_widget_queue_resize, vFp)
GO(gtk_widget_queue_resize_no_redraw, vFp)
GO(gtk_widget_realize, vFp)
GO(gtk_widget_ref, pFp) // Warning: failed to confirm
GO(gtk_widget_region_intersect, pFpp)
GO(gtk_widget_register_window, vFpp)
GO(gtk_widget_remove_accelerator, iFppuu)
GO(gtk_widget_remove_mnemonic_label, vFpp)
GO(gtk_widget_render_icon, pFppup)
GO(gtk_widget_reparent, vFpp)
GO(gtk_widget_reset_rc_styles, vFp)
GO(gtk_widget_reset_shapes, vFp) // Warning: failed to confirm
GO(gtk_widget_send_expose, iFpp)
GO(gtk_widget_send_focus_change, iFpp)
GO(gtk_widget_set, vFppppppppppppppp) // Warning: failed to confirm
GO(gtk_widget_set_accel_path, vFppp)
GO(gtk_widget_set_allocation, vFpp)
GO(gtk_widget_set_app_paintable, vFpi)
GO(gtk_widget_set_can_default, vFpi)
GO(gtk_widget_set_can_focus, vFpi)
GO(gtk_widget_set_child_visible, vFpi)
GO(gtk_widget_set_clip, vFpp)
GO(gtk_widget_set_colormap, vFpp) // Warning: failed to confirm
GO(gtk_widget_set_composite_name, vFpp)
GO(gtk_widget_set_css_classes, vFpp) // Warning: failed to confirm
GO(gtk_widget_set_default_colormap, vFp) // Warning: failed to confirm
GO(gtk_widget_set_default_direction, vFu)
GO(gtk_widget_set_direction, vFpu)
GO(gtk_widget_set_double_buffered, vFpi)
GO(gtk_widget_set_events, vFpi)
GO(gtk_widget_set_extension_events, vFpi) // Warning: failed to confirm
GO(gtk_widget_set_halign, vFpu)
GO(gtk_widget_set_has_tooltip, vFpi)
GO(gtk_widget_set_has_window, vFpi)
GO(gtk_widget_set_hexpand, vFpi)
GO(gtk_widget_set_hexpand_set, vFpi)
GO(gtk_widget_set_mapped, vFpi)
GO(gtk_widget_set_margin_bottom, vFpi)
GO(gtk_widget_set_margin_end, vFpi)
GO(gtk_widget_set_margin_left, vFpi)
GO(gtk_widget_set_margin_right, vFpi)
GO(gtk_widget_set_margin_start, vFpi)
GO(gtk_widget_set_margin_top, vFpi)
GO(gtk_widget_set_name, vFpp)
GO(gtk_widget_set_no_show_all, vFpi)
GO(gtk_widget_set_parent, vFpp)
GO(gtk_widget_set_parent_window, vFpp)
GO(gtk_widget_queue_compute_expand, vFp)
GO(gtk_widget_set_realized, vFpi)
GO(gtk_widget_set_receives_default, vFpi)
GO(gtk_widget_set_redraw_on_allocate, vFpi)
GO(gtk_widget_set_scroll_adjustments, iFppp) // Warning: failed to confirm
GO(gtk_widget_set_sensitive, vFpi)
GO(gtk_widget_set_size_request, vFpii)
GO(gtk_widget_set_state, vFpu)
GO(gtk_widget_set_state_flags, vFpui)
GO(gtk_widget_set_style, vFpp)
GO(gtk_widget_class_set_template, vFpp)
GO(gtk_widget_class_set_template_from_resource, vFpp)
GO(gtk_widget_set_tooltip_markup, vFpp)
GO(gtk_widget_set_tooltip_text, vFpp)
GO(gtk_widget_set_tooltip_window, vFpp)
GO(gtk_widget_set_uposition, vFpii) // Warning: failed to confirm
GO(gtk_widget_set_usize, vFpii) // Warning: failed to confirm
GO(gtk_widget_set_valign, vFpu)
GO(gtk_widget_set_vexpand, vFpi)
GO(gtk_widget_set_vexpand_set, vFpi)
GO(gtk_widget_set_visible, vFpi)
GO(gtk_widget_set_window, vFpp)
GO(gtk_widget_shape_combine_mask, vFppii) // Warning: failed to confirm
GO(gtk_widget_show, vFp)
GO(gtk_widget_show_all, vFp)
GO(gtk_widget_show_now, vFp)
GO(gtk_widget_size_allocate, vFpp)
GO(gtk_widget_size_request, vFpp)
GO(gtk_widget_style_attach, vFp)
GOM(gtk_widget_style_get, vFEppV)
GO(gtk_widget_style_get_property, vFppp)
//GOM(gtk_widget_style_get_valist, vFppA)
GO(gtk_widget_thaw_child_notify, vFp)
GO(gtk_widget_translate_coordinates, iFppiipp)
GO(gtk_widget_trigger_tooltip_query, vFp)
GO(gtk_widget_unmap, vFp)
GO(gtk_widget_unparent, vFp)
GO(gtk_widget_unrealize, vFp)
GO(gtk_widget_unref, vFp) // Warning: failed to confirm
GO(gtk_window_activate_default, iFp)
GO(gtk_window_activate_focus, iFp)
GO(gtk_window_activate_key, iFpp)
GO(gtk_window_add_accel_group, vFpp)
GO(gtk_window_add_embedded_xid, vFpu) // Warning: failed to confirm
GO(gtk_window_add_mnemonic, vFpup)
GO(gtk_window_begin_move_drag, vFpiiiu)
GO(gtk_window_begin_resize_drag, vFpuiiiu)
GO(gtk_window_close, vFp)
GO(gtk_window_deiconify, vFp)
GO(gtk_window_destroy, vFp) // Warning: failed to confirm
GO(gtk_window_fullscreen, vFp)
GO(gtk_window_get_accept_focus, iFp)
GO(gdk_window_get_clip_region, pFp)
GO(gtk_window_get_decorated, iFp)
GO(gtk_window_get_default_icon_list, pFv)
GO(gtk_window_get_default_icon_name, pFv)
GO(gtk_window_get_default_size, vFppp)
GO(gtk_window_get_default_widget, pFp)
GO(gtk_window_get_deletable, iFp)
GO(gtk_window_get_destroy_with_parent, iFp)
GO(gtk_window_get_focus, pFp)
GO(gtk_window_get_focus_on_map, iFp)
GO(gtk_window_get_frame_dimensions, vFppppp) // Warning: failed to confirm
GO(gtk_window_get_gravity, uFp)
GO(gtk_window_get_group, pFp)
GO(gtk_window_get_has_frame, iFp) // Warning: failed to confirm
GO(gtk_window_get_has_resize_grip, iFp)
GO(gtk_window_get_icon, pFp)
GO(gtk_window_get_icon_list, pFp)
GO(gtk_window_get_icon_name, pFp)
GO(gtk_window_get_mnemonic_modifier, uFp)
GO(gtk_window_get_mnemonics_visible, iFp)
GO(gtk_window_get_modal, iFp)
GO(gtk_window_get_opacity, dFp)
GO(gtk_window_get_position, vFppp)
GO(gtk_window_get_resizable, iFp)
GO(gtk_window_get_role, pFp)
GO(gdk_window_get_scale_factor, iFp)
GO(gtk_window_get_screen, pFp)
GO(gtk_window_get_size, vFppp)
GO(gtk_window_get_skip_pager_hint, iFp)
GO(gtk_window_get_skip_taskbar_hint, iFp)
GO(gtk_window_get_title, pFp)
GO(gtk_window_get_transient_for, pFp)
GO(gtk_window_get_type, LFv)
GO(gtk_window_get_type_hint, uFp)
GO(gtk_window_get_urgency_hint, iFp)
GO(gtk_window_get_window_type, uFp)
GO(gtk_window_group_add_window, vFpp)
GO(gtk_window_group_get_current_grab, pFp)
GO(gtk_window_group_get_type, LFv)
GO(gtk_window_group_list_windows, pFp)
GO(gtk_window_group_new, pFv)
GO(gtk_window_group_remove_window, vFpp)
GO(gtk_window_has_group, iFp)
GO(gtk_window_has_toplevel_focus, iFp)
GO(gtk_window_iconify, vFp)
GO(gtk_window_is_active, iFp)
GO(gtk_window_list_toplevels, pFv)
GO(gtk_window_maximize, vFp)
GO(gtk_window_mnemonic_activate, iFpuu)
GO(gtk_window_move, vFpii)
GO(gtk_window_new, pFu)
GO(gtk_window_parse_geometry, iFpp)
GO(gtk_window_position_get_type, LFv)
GO(gtk_window_present, vFp)
GO(gtk_window_present_with_time, vFpu)
GO(gtk_window_propagate_key_event, iFpp)
GO(gtk_window_remove_accel_group, vFpp)
GO(gtk_window_remove_embedded_xid, vFpu) // Warning: failed to confirm
GO(gtk_window_remove_mnemonic, vFpup)
GO(gtk_window_reshow_with_initial_size, vFp)
GO(gtk_window_resize, vFpii)
GO(gtk_window_set_accept_focus, vFpi)
GO(gtk_window_set_auto_startup_notification, vFi)
GO(gtk_window_set_decorated, vFpi)
GO(gtk_window_set_default, vFpp)
GO(gtk_window_set_default_icon, vFp)
GO(gtk_window_set_default_icon_from_file, iFpp)
GO(gtk_window_set_default_icon_list, vFp)
GO(gtk_window_set_default_icon_name, vFp)
GO(gtk_window_set_default_size, vFpii)
GO(gtk_window_set_deletable, vFpi)
GO(gtk_window_set_destroy_with_parent, vFpi)
GO(gtk_window_set_focus, vFpp)
GO(gtk_window_set_focus_on_map, vFpi)
GO(gtk_window_set_frame_dimensions, vFpiiii) // Warning: failed to confirm
GO(gtk_window_set_geometry_hints, vFpppu)
GO(gtk_window_set_gravity, vFpu)
GO(gtk_window_set_has_frame, vFpi) // Warning: failed to confirm
GO(gtk_window_set_hide_on_close, vFpi) // Warning: failed to confirm
GO(gtk_window_set_icon, vFpp)
GO(gtk_window_set_icon_from_file, iFppp)
GO(gtk_window_set_icon_list, vFpp)
GO(gtk_window_set_icon_name, vFpp)
GO(gtk_window_set_keep_above, vFpi)
GO(gtk_window_set_keep_below, vFpi)
GO(gtk_window_set_mnemonic_modifier, vFpu)
GO(gtk_window_set_mnemonics_visible, vFpi)
GO(gtk_window_set_modal, vFpi)
GO(gtk_window_set_opacity, vFpd)
GO(gtk_window_set_policy, vFpiii) // Warning: failed to confirm
GO(gtk_window_set_position, vFpu)
GO(gtk_window_set_resizable, vFpi)
GO(gtk_window_set_role, vFpp)
GO(gtk_window_set_screen, vFpp)
GO(gtk_window_set_skip_pager_hint, vFpi)
GO(gtk_window_set_skip_taskbar_hint, vFpi)
GO(gtk_window_set_startup_id, vFpp)
GO(gtk_window_set_title, vFpp)
GO(gtk_window_set_transient_for, vFpp)
GO(gtk_window_set_type_hint, vFpu)
GO(gtk_window_set_titlebar, vFpp)
GO(gtk_window_set_urgency_hint, vFpi)
GO(gtk_widget_set_visual, vFpp)
GO(gtk_window_set_wmclass, vFppp)
GO(gtk_window_stick, vFp)
GO(gtk_window_type_get_type, LFv)
GO(gtk_window_unfullscreen, vFp)
GO(gtk_window_unmaximize, vFp)
GO(gtk_window_unstick, vFp)
GO(gtk_wrap_mode_get_type, LFv)
GO(gtk_gesture_long_press_get_type, LFv)
GO(gtk_gesture_single_get_type, LFv)
GO(gtk_gesture_get_type, LFv)
GO(gtk_gesture_rotate_new, pFp)
GO(gtk_gesture_zoom_new, pFp)
GO(gtk_event_controller_get_type, LFv)
GO(gtk_stack_set_visible_child_name, vFpp)
GO(gtk_stack_get_visible_child_name, pFp)

GO(dummy_iFppdd, iFppdd)    // for GtkEventController wrapping
GO(dummy_iFppUup, iFppUup)
GO(dummy_pFpLi, pFpLi)
